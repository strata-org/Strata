PORT ?= 1080
BOOKS := ddm langdef laurel transforms

.PHONY: $(BOOKS) all clean build-% serve-%

# `make <book>` builds and serves; `make build-<book>` builds only (no
# blocking http.server, e.g. for vim's `:make`).
$(BOOKS): %: build-% serve-%

build-%:
	lake exe $* --with-html-single --output _out/$*

build-langdef:
	lake exe langdef --with-html-single --output _out/langdef
	cp strata-hourglass.png _out/langdef/html-single/

serve-%:
	@(sleep 1 && open http://localhost:$(PORT)/) &
	python3 -m http.server $(PORT) -d _out/$*/html-single

all:
	./generate.sh

clean:
	rm -rf _out
