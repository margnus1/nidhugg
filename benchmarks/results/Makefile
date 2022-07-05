SUBDIRS =			\
	event_driven/2_phase_commit \
	event_driven/n_buyers 	    \
	event_driven/nW 	\
	event_driven/n2W 	\
	event_driven/multilevel_race 	\
	event_driven/nR+nR 	\
	event_driven/n_msgs_nW+nR 	\
	event_driven/ping_pong 	    \
	event_driven/consensus

# T ?= all

TABULATE = ./tabulate.sh

all: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@ $(T)

all_merged.txt: all
	$(TABULATE) all_merge $(SUBDIRS)

mrproper:
	for d in $(SUBDIRS); do \
		$(MAKE) -C$$d mrproper; \
	done
	rm -f all_merged.txt

.PHONY: $(SUBDIRS) all mrproper
