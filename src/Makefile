include Makefile.config

ICFLAGS = \
-I$(GMP_PREFIX)/include \
-I$(MPFR_PREFIX)/include \
-I$(APRON_PREFIX)/include \
-Wall -Wstrict-prototypes -Wimplicit-function-declaration \
-std=c99
# -Winline -Wconversion

LCFLAGS = \
-L$(JSTAR_PREFIX)/lib \
-L$(GMP_PREFIX)/lib \
-L$(MPFR_PREFIX)/lib \
-L$(APRON_PREFIX)/lib \
-L$(PPL_PREFIX)/lib \
-L$(CAMLIDL_PREFIX)/lib/ocaml

OCAMLINC = \
-I $(JSTAR_PREFIX)/lib \
-I $(JSTAR_PREFIX)/src/utils \
-I $(JSTAR_PREFIX)/src/prover_syntax \
-I $(JSTAR_PREFIX)/src/plugin_interface \
-I $(MLGMPIDL_PREFIX)/lib \
-I $(APRON_PREFIX)/lib

OCAMLLDFLAGS = \
-noautolink -ccopt "$(LCFLAGS)" \
bigarray.cma gmp.cma apron.cma box.cma polka.cma debug.cmi prover_syntax.a plugin.cmi plugin_callback.cmi \
-cclib "-lpolkaRll_caml -lpolkaRll_debug -loctD_caml -loctD -lboxD_caml -lboxD_debug -litv_debug -lapron_caml_debug -lapron_debug -lgmp_caml -lmpfr -lgmpxx -lgmp -lbigarray -lcamlidl"

OCAMLOPTLDFLAGS = \
-noautolink -verbose -ccopt "$(LCFLAGS)" \
bigarray.cmxa gmp.cmxa apron.cmxa box.cmxa polka.cmxa debug.cmx prover_syntax.cmxa plugin.cmx plugin_callback.cmx \
-cclib "-lpolkaRll_caml -lpolkaRll_debug -loctD_caml -loctD -lboxD_caml -lboxD_debug -litv_debug -lapron_caml_debug -lapron_debug -lgmp_caml -lmpfr -lgmpxx -lgmp -lbigarray -lcamlidl"

ifndef BIN
	BIN := ../bin
endif
export BIN


default: all

all: num_abs.cmxs

%.cmxs: %.cmx
	$(OCAMLOPT) $(OCAMLOPTFLAGS) $(OCAMLINC) $(OCAMLOPTLDFLAGS) -shared -o $(BIN)/$@ $<

%.opt: %.cmx
ifeq ($(shell uname -o), Cygwin)
	$(OCAMLOPT) -cc "flexlink -chain cygwin -exe " $(OCAMLOPTFLAGS) $(OCAMLINC) $(OCAMLOPTLDFLAGS) -o $(BIN)/$@ $<
else
	$(OCAMLOPT) -cc "g++" $(OCAMLOPTFLAGS) $(OCAMLINC) $(OCAMLOPTLDFLAGS) -o $(BIN)/$@ $<
endif

%: %.cmo $(APRON_PREFIX)/bin/apronrun
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) $(OCAMLLDFLAGS) -g -use-runtime $(APRON_PREFIX)/bin/apronrun -o $@ $<

%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) -c -o $@ $<

%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) $(OCAMLINC) -c -o $@ $<

clean:
	rm -f *.cm[ioxa] *.o
