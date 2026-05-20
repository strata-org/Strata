PORT ?= 1080
BOOKS := ddm langdef laurel transforms

.PHONY: $(BOOKS) all clean build-% serve-%

$(BOOKS): %: build-% serve-%

build-%:
	lake exe $* --with-html-single --output _out/$*
	@if [ "$*" = "langdef" ]; then cp strata-hourglass.png _out/langdef/html-single/; fi

serve-%:
	@(sleep 1 && open http://localhost:$(PORT)/) &
	python3 -m http.server $(PORT) -d _out/$*/html-single

all:
	./generate.sh

clean:
	rm -rf _out
