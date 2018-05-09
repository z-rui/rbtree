#!/bin/sh

ctangle rbtree
cweave rbtree
tex '\let\pdf+ \input rbtree'
dvipdfm rbtree
