
# Using 'help2man' to create man pages (does not work with Å):

# In 'configure.ac' put
# AM_MISSING_PROG(HELP2MAN, help2man, $missing_dir)
#
# In ../Makefile.am, add 'man' to SUBDIRS or EXTRA_DIST.

dist_man1_MANS = mli.man

mli.man: ../src/mli
	-$(HELP2MAN) --output=$@ --locale=en_US.UTF-8 --name='GNU MLI, MetaLogic Inference' ../src/mli
	-mv mli.man $(srcdir)

