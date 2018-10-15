all: 
	$(MAKE) -C src
	cp src/xduce.opt .

debug: 
	$(MAKE) -C src debug
	cp src/xduce .

clean:
	-rm *~ doc/*~ lib/*~ xduce.opt xduce gmon.out
	-$(MAKE) -C examples clean
	-$(MAKE) -C src clean

# RELEASING
# How to release:
# 1) Release preparation
# - increment the RELEASE variable in Makefile
# - modify CHANGES and doc/README.html
# - "make release-prep"
# - make sure everything committed
# - "make release-test"
# 2) Release
# - "make snapshot"
# - "make release"
# - "make upload"
# - go to SourceForge releasing page

RELEASE = 0.5.0
RELEASETAG = xduce-$(shell echo $(RELEASE) | tr . _)

TEMP = /tmp/xducetest

#CVSROOT = :pserver:anonymous@cvs.sourceforge.net:/cvsroot/xduce
CVSROOT = :ext:hahosoya@cvs.sourceforge.net:/cvsroot/xduce

release-test:
	@rm -rf $(TEMP)
	mkdir $(TEMP)
	cd $(TEMP); cvs -d$(CVSROOT) -z3 checkout xduce
	cd $(TEMP)/xduce/xduce; $(MAKE) release-test2

release-test2:
	$(MAKE) all
	$(MAKE) -C examples test
	@echo "************* Seems alright **************"

release-prep:
	lynx -dump doc/README.html > README

snapshot:
	cvs -d$(CVSROOT) tag $(RELEASETAG)

release:
	rm -rf $(TEMP)
	mkdir $(TEMP)
	cd $(TEMP); cvs -d$(CVSROOT) -z3 export -r $(RELEASETAG) xduce; cd xduce; mv xduce xduce-$(RELEASE); tar cvf $(TEMP)/xduce-$(RELEASE).tar xduce-$(RELEASE); gzip $(TEMP)/xduce-$(RELEASE).tar

upload:
	ncftpput -v upload.sourceforge.net /incoming $(TEMP)/xduce-$(RELEASE).tar.gz


test:
	-$(MAKE) -C examples test
