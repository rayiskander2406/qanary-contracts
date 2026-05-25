#!/usr/bin/perl
# Convert pandoc longtable -> table*+tabular so it compiles under IEEEtran
# two-column (longtable is incompatible with twocolumn). v2 adds caption
# relocation: pandoc emits \caption{...}\tabularnewline INSIDE the longtable
# (after the colspec), which would be invalid inside a tabular; v2 hoists the
# caption to sit between \begin{table*} and \begin{tabular} (IEEE places table
# captions above the table).
#
# Pandoc invariant: colspec opens "\begin{longtable}[]{@{}" and closes with a
# line ending in "@{}}" (possibly the same line). A caption, when present,
# immediately follows the colspec as "\caption{...}" possibly spanning lines,
# terminated by "\tabularnewline".
use strict; use warnings;

my $in_spec = 0;
my @spec;
my $pending_tabular = '';   # holds "\begin{tabular}{...}\n" until caption resolved
my $cap_mode = 0;
my @cap;
my $skip_head = 0;          # drop the duplicated header pandoc emits for captioned tables

while (my $l = <>) {
    # --- colspec collection ---
    if (!$in_spec && $l =~ /^\\begin\{longtable\}\[\]\{/) {
        $in_spec = 1; @spec = ($l);
        if ($l =~ /\@\{\}\}\s*$/) { $in_spec = 0; open_table(@spec); }
        next;
    }
    if ($in_spec) {
        push @spec, $l;
        if ($l =~ /\@\{\}\}\s*$/) { $in_spec = 0; open_table(@spec); }
        next;
    }

    # --- caption capture (only while a tabular is pending) ---
    if ($pending_tabular ne '' && !$cap_mode && $l =~ /^\\caption\{/) {
        $cap_mode = 1; @cap = ($l);
        if ($l =~ /\\tabularnewline/) { $cap_mode = 0; flush_caption_then_tabular(); }
        next;
    }
    if ($cap_mode) {
        push @cap, $l;
        if ($l =~ /\\tabularnewline/) { $cap_mode = 0; flush_caption_then_tabular(); }
        next;
    }

    # --- first non-caption line after colspec: flush bare tabular ---
    if ($pending_tabular ne '') { print $pending_tabular; $pending_tabular = ''; }

    # Captioned longtables repeat the header (firsthead + head). Keep the
    # firsthead's header; drop the duplicate head block (everything from
    # \endfirsthead through \endhead inclusive).
    if ($l =~ /^\s*\\endfirsthead\s*$/) { $skip_head = 1; next; }
    if ($skip_head) { $skip_head = 0 if $l =~ /^\s*\\endhead\s*$/; next; }

    $l =~ s/\\noalign\{\}//g;
    next if $l =~ /^\s*\\end(head|firsthead|lastfoot|foot)\s*$/;
    if ($l =~ /^\\end\{longtable\}/) { print "\\end{tabular}\n\\end{table*}\n"; next; }
    print $l;
}

sub open_table {
    my $s = join('', @_);
    $s =~ s/^\\begin\{longtable\}\[\]\{//;    # strip opener
    $s =~ s/\@\{\}\}\s*$//;                   # strip closing @{}}
    $s =~ s/^\s*\@\{\}//;                     # strip leading @{}
    $s =~ s/\s+/ /g;                          # flatten whitespace
    print "\\begin{table*}[!t]\\footnotesize\\centering\n";
    $pending_tabular = "\\begin{tabular}{\@{}$s\@{}}\n";
}

sub flush_caption_then_tabular {
    my $cap = join('', @cap);
    $cap =~ s/\\tabularnewline\s*$//;         # drop the terminating \tabularnewline
    $cap =~ s/\s+$//;                          # trim trailing ws
    print "$cap\n";                            # \caption{...} above the tabular
    print $pending_tabular;
    $pending_tabular = '';
}
