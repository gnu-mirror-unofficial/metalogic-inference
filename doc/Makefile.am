
info_TEXINFOS = mli.texi

dist_doc_DATA = mli.pdf classes.pdf classes.gv
dist_noinst_DATA = mli.tex version.texi luatex-math-modified.tex gpl-3.0.texi  texinfo.tex


TEXI2PDF = ':'

mli.texi: mli.tex
	awk '!/@stixfont/' $(srcdir)/mli.tex > $(srcdir)/mli.texi

# Indexing: luatex mli.tex cretest the unsorted mli.?p index files, and texindex mli.??
# creates the sorted texindex mli.??s files, which are used in the mli.pdf index. Several runs 
# may be required to get the index right, cf. the Texinfo manual, sec. 19.3.
mli.pdf: mli.tex
	cd $(srcdir) && luatex mli.tex && texindex mli.??

classes.pdf: classes.gv
	-cd $(srcdir) && dot -Tpdf classes.gv -o classes.pdf




