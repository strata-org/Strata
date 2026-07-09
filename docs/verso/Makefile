PORT ?= 1080
BOOKS := ddm langdef laureldesign laurelimpl laurelguide transforms

.PHONY: $(BOOKS) all clean build-% serve-%

$(BOOKS): %: build-% serve-%

build-%:
	lake exe $* --with-html-single --output _out/$*

build-langdef:
	lake exe langdef --with-html-single --output _out/langdef
	cp strata-hourglass.png _out/langdef/html-single/

build-laurelguide:
	lake exe laurelguide --with-html-multi --output _out/laurelguide

build-laureldesign:
	lake exe laureldesign --with-html-multi --output _out/laureldesign

build-laurelimpl:
	lake exe laurelimpl --with-html-multi --output _out/laurelimpl

serve-%:
	@(sleep 1 && open http://localhost:$(PORT)/) &
	python3 -m http.server $(PORT) -d _out/$*/html-single

serve-laurelguide:
	@(sleep 1 && open http://localhost:$(PORT)/) &
	python3 -m http.server $(PORT) -d _out/laurelguide/html-multi

serve-laureldesign:
	@(sleep 1 && open http://localhost:$(PORT)/) &
	python3 -m http.server $(PORT) -d _out/laureldesign/html-multi

serve-laurelimpl:
	@(sleep 1 && open http://localhost:$(PORT)/) &
	python3 -m http.server $(PORT) -d _out/laurelimpl/html-multi

all:
	./generate.sh

clean:
	rm -rf _out
