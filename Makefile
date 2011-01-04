build:
	mkdir -p bin
	$(MAKE) -C src

test: build
	$(MAKE) -s -C unit_tests

clean:
	rm -f bin/*
	$(MAKE) -C src clean
	$(MAKE) -C unit_tests clean

.PHONY: build test test clean
