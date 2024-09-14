# -*- Makefile -*-

#SUBDIRS = simulation library core drivers
#SUBDIRS = utils library simulation drivers guests test core
SUBDIRS = utils library drivers guests test core simulation
#SUBDIRS = library simulation guests core

all:
	set -e; for d in $(SUBDIRS); do $(MAKE) -C $$d ; done

clean:
	for d in $(SUBDIRS); do $(MAKE) clean -C $$d ; done
	rm -rf bin
# testing
test: all
	make -C test test
.PHONY: test

setup:
	cd ../sth-linux; ./build.sh; ./deploy.sh; cd -

deploy: 
	./deploy.sh

run:	setup all deploy
	./uart_screen.sh; reset

##
sim: all
	make -C core sim
