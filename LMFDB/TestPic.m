// Usage: ls pic_examples | parallel -j32 --timeout 600 "magma -b isocls:={1} TestPic.m > output/{1} &2>1"

SetColumns(0);
SetVerbose("User1", 1);

base:="/home/roed/266_wk_icm_rec/labelling/parallel/";
AttachSpec(base*"AlgEt/spec");
Attach(base*labeling.m);
Attach("packages.spec");
Attach("LMFDB/Picardext.m");
schema := Read("LMFDB/pic_examples/" * isocls);
R:=LoadSchemaWKClasses(schema);
t0 := Cputime();
B:=CanonicalPicBasis(R);
printf "Complete in %o\n", Cputime() - t0;
quit;