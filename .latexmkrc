system("bash ./scripts/init-missing-lagda.sh");

add_cus_dep('lagda','tex',0,'lagda2tex');

@default_files = ('paper.tex');

sub lagda2tex {
    my $base = shift @_;
    return system("bash ./scripts/agda-from-toplevel.sh $base.lagda");
}
