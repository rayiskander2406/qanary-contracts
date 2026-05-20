#!/usr/bin/perl
# Measurement-only: convert pandoc longtable -> table+tabular so it compiles
# under IEEEtran two-column (longtable is incompatible with twocolumn).
# Pandoc invariant: colspec opens "\begin{longtable}[]{@{}" and closes with
# a line ending in "@{}}" (possibly the same line for single-line specs).
use strict; use warnings;
my $in_spec = 0;
my @spec;
while (my $l = <>) {
    if (!$in_spec && $l =~ /^\\begin\{longtable\}\[\]\{/) {
        $in_spec = 1; @spec = ($l);
        if ($l =~ /\@\{\}\}\s*$/) {           # whole spec on one line
            $in_spec = 0;
            print emit_tabular(@spec);
        }
        next;
    }
    if ($in_spec) {
        push @spec, $l;
        if ($l =~ /\@\{\}\}\s*$/) {           # colspec close
            $in_spec = 0;
            print emit_tabular(@spec);
        }
        next;
    }
    $l =~ s/\\noalign\{\}//g;
    next if $l =~ /^\s*\\end(head|firsthead|lastfoot|foot)\s*$/;
    if ($l =~ /^\\end\{longtable\}/) { print "\\end{tabular}\n\\end{table*}\n"; next; }
    print $l;
}
sub emit_tabular {
    my $s = join('', @_);
    $s =~ s/^\\begin\{longtable\}\[\]\{//;    # strip opener
    $s =~ s/\@\{\}\}\s*$//;                   # strip closing @{}}
    $s =~ s/^\s*\@\{\}//;                     # strip leading @{}
    $s =~ s/\s+/ /g;                          # flatten whitespace
    return "\\begin{table*}[!t]\\footnotesize\\centering\n\\begin{tabular}{\@{}$s\@{}}\n";
}
