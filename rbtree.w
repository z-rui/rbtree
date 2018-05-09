\input epsf
\def\figure#1{\ifmmode\vcenter{\hbox{\figure{#1}}}\else\epsfbox{#1}\fi}
\def\overrightarrow#1{\vcenter{\offinterlineskip
  \halign{\hfil##\hfil\cr
  \sevenrm\enspace#1\enspace\mathstrut\cr
  \rightarrowfill\cr}}}
\def\overunder#1#2#3{\vcenter{\offinterlineskip
  \halign{\hfil##\hfil\cr
  \sevenrm\enspace#2\enspace\mathstrut\cr
  #1\cr
  \sevenrm\enspace#3\enspace\mathstrut\cr}}}
\def\overunderleftarrow#1#2{\overunder{\leftarrowfill\cr}{#1}{#2}}
\def\overunderrightarrow#1#2{\overunder{\rightarrowfill\cr}{#1}{#2}}
\def\overunderleftrightarrow#1#2{\overunder{%
  \rightarrowfill\cr\leftarrowfill\cr}{#1}{#2}}

\mathchardef\bigO="704F

@* Introduction.
This is my implementation of a red-black tree.

A red-black tree is a balanced binary search tree.
It guarantees that its height is $\bigO(\log n)$, where $n$ is the number
of nodes in the tree.
As a result, usual operations like search, insertion and deletion can be done
in logarithmic time.

When a binary search tree (BST) is not balanced,
it may degrade to a linked list, and the performance becomes worse.

Red-black trees are often compared with AVL trees as they are both
balanced BSTs.  The latter is more strictly balanced, which results in
a smaller height.

Some other BSTs may only guarantee {\it amortized\/} time complexity,
meaning that $m$ sequential operations take $\bigO(m\log n)$ time.
They may have other intersting properties, though.

@ A red-black tree is a binary search tree whose nodes
are (unsurprisingly) either red or black.
Further more, the following invariants have to be satisfied:
@!@^Invariants@>
\smallskip
\item{1.}  The root is black.
\item{2.}  Red nodes can only have black children.
\item{3.}  Every path from root to |NULL| has the same number of black nodes.
\smallskip

Here |NULL| is a dummy node, which merely means ``no node''.
If some node does not have a left or right child, we say that child is |NULL|.
For convenience, the color of |NULL| is considered black.

@ In my implementation, a node in the red-black tree contains
a parent pointer and two child pointers.
|child[0]| and |child[1]| refer to the left and the right child respectively.
This notation helps merging code for symmetric cases.

@s uintptr_t int
@d LEFT 0
@d RIGHT 1
@(rbtree.h@>=
#ifndef RBTREE_H
#define RBTREE_H

#include <stdint.h> /* for |uintptr_t| */
struct rb_node {
	uintptr_t parent_color;
	struct rb_node *child[2];
};

@<exported functions@>@;
#endif

@ Some bitwise tricks are used here,
in order to encode information in the unused bits of a pointer:
the color of a node is stored at the lowest bit of its |parent_color| field.

This works because on my machine, the lowest bit of a pointer is always zero,
due to alignment requirements.  This is not portable.
However, as far as I know, many others do the same trick,
so it may be not so non-portable as it seems to be\dots

@d RED_MASK ((uintptr_t) 1)
@d PTR_MASK (~RED_MASK)
@d IS_RED(x) ((x)?(x)->parent_color&RED_MASK:0)
@d SET_RED(x) ((x)->parent_color|=RED_MASK)
@d SET_BLK(x) ((x)->parent_color&=~RED_MASK)
@d PARENT(x) ((struct rb_node *)((x)->parent_color&PTR_MASK))
@d SET_PARENT(x, p)
	((x)->parent_color=(uintptr_t)p|((x)->parent_color&RED_MASK))
@c
#include "rbtree.h" /* for |struct rb_node| */
#include <stddef.h> /* for |NULL| */

@* Debugging.
Writing code mixing pointers and bitwise operations is a total mess.
Moreover, implementing a red-black tree is not an easy task.
I'm expecting a huge amount of bugs during the development.
It's a good time now to write some debugging functions first.

@c
#include <assert.h>
#ifndef NDEBUG
#include <stdio.h>
@<debugging functions@>@;
#endif

@
@<debugging...@>+=
void rb_debug_tree(struct rb_node *root,
		void (*callback)(const struct rb_node *))
{
	fputc('(', stderr);
	if (root != NULL) {
		if (callback)
			callback(root);
		else
			fprintf(stderr, "%p", root);
		fprintf(stderr, ":%c", IS_RED(root) ? 'R' : 'B');
		rb_debug_tree(root->child[LEFT], callback);
		rb_debug_tree(root->child[RIGHT], callback);
	}
	fputc(')', stderr);
}

@
@<debugging...@>+=
static void checknode(struct rb_node *node, struct rb_node *parent)
{
	if (node == NULL) return;
	assert(PARENT(node) == parent);
	if (IS_RED(node)) {
		assert(!IS_RED(node->child[LEFT]) &&
				!IS_RED(node->child[RIGHT]));
	}
	checknode(node->child[LEFT], node);
	checknode(node->child[RIGHT], node);
}

static void checkpath(struct rb_node *root, long cnt, long *path)
{
	if (root == NULL) {
		if (*path == -1)
			*path = cnt;
		else
			assert(*path == cnt);
	} else {
		if (!IS_RED(root))
			cnt++;
		checkpath(root->child[LEFT], cnt, path);
		checkpath(root->child[RIGHT], cnt, path);
	}
}

void rb_checkinvariants(struct rb_node *root)
{
	long path = -1;
	assert(!IS_RED(root));
	checknode(root, NULL);
	checkpath(root, 0, &path);
}

@* Rotation.
The basic operation that keeps the tree balanced is called {\it rotation}.
Rotations keeps the property of a binary search tree.
There are 4~kinds of rotations: $\{\hbox{single},\hbox{double}\}\times
\{\hbox{left},\hbox{right}\}$ rotation.

@ Single rotation.
Tree rotations are best described by pictures.
Below is the picture showing a single rotation.
$$\figure{rbtree.1}\quad
\overunderleftrightarrow{right rotation}{left rotation}\quad
\figure{rbtree.2}$$
Obviously, the two operations are symmetric.

Function |single_rotation| does a |dir|-rotation, depending on
the value of |dir| being |LEFT| or |RIGHT|.
If you want to study the left rotation,
treat all |dir| in the code as |LEFT|, and |!dir| as |RIGHT|;
and do the opposite for the right rotation.

@c
static void single_rotation(struct rb_node **link, int dir)
{
	struct rb_node *x, *y, *z;

	@<compute pointers |x|, |y| and |z| for rotation@>@;
	@<make |z| the |!dir|-child of |x|@>@;
	@<make |y| the root, |x| the |dir|-child of |y|; swap their color@>@;
}

@  When doing single rotations, both |x| and |y| must not be |NULL|.
(Think about it: if |x==NULL|, what on earth is |y|?
If |y==NULL|, what will be the new root?)

@<compute pointers |x|, |y| and |z| for rotation@>=
x = *link;
assert(x != NULL);
y = x->child[!dir];
assert(y != NULL);
z = y->child[dir];

@ My first step is to change |z| so that |x| will be its parent.
The following picture shows the transformation in a right rotation.
$$\figure{rbtree.1}\quad\longrightarrow
\hskip.5em % spacing is a little bit awkward (asymmetric)
\figure{rbtree.3}$$
I need to update |z|'s parent pointer, but only if |z!=NULL|.
After this step, |y| will be in a wrong state
(its parent pointer still points to |x|, and its |dir|-child pointer
still points to |z|).  This will be fixed in later steps.
@<make |z| the |!dir|-child of |x|@>=
if (z != NULL)
	SET_PARENT(z, x);
x->child[!dir] = z;

@ The second step is to make |y| the root.
$$\figure{rbtree.3}\hskip.5em
\longrightarrow\quad\figure{rbtree.2}$$

Why swap the color of |x| and |y|?
(TODO: more explanations.)

@<make |y| the root...@>=
{
	uintptr_t t = y->parent_color & RED_MASK;
	y->parent_color = x->parent_color;
	x->parent_color= (uintptr_t) y | t;
}
*link = y;
y->child[dir] = x;

@ Double rotation.
A single rotation does not change the depth of |z| in the figures.
When I want to move |z| up, I need a double rotation:
$$\figure{rbtree.5}\quad
\overunderrightarrow{double rotation}{right}
\figure{rbtree.7} % weird, no \quad looks better...
\overunderleftarrow{double rotation}{left}
\quad\figure{rbtree.6}$$
A double rotation can be seen as two single rotations.
For example, a double right rotation on |x|
(in the leftmost tree in the figure) is a single left rotation on |y|
followed by a single right rotation on |x|.

@c
static void double_rotation(struct rb_node **link, int dir)
{
	single_rotation(&(*link)->child[!dir], !dir);
	single_rotation(link, dir);
}

@* Search.
The good news is that searching in a red-black tree is the same as in
an ordinary BST.
So there is no need to write again the well-known algorithm.

Well, I decided to write it anyway,
just in case the user don't know how to search a BST (too bad!).

@<exported functions@>+=
extern struct rb_node **
rb_find(struct rb_node **, struct rb_node **,@|
		const void *, int @[@](*)(const void *, const void *));

@
As in other \CEE/ routines, it uses a function pointer taking |void *|
arguments for comparison.

Copying the following code (with minor changes)
and make a customized search function can reduce the overhead.
For simple key types, the saving can be significant.
However, for complex key types, it's likely that
the user has to call a comparison function anyway\dots

@c
struct rb_node **
rb_find(struct rb_node **link, struct rb_node **parent,@|
		const void *key, int @[@](*compar)(const void *, const void *))
{
	struct rb_node *node;

	*parent = NULL;
	while ((node = *link) != NULL) {
		int cmp;

		cmp = (*compar)(key, node);
		if (cmp < 0)
			link = &node->child[LEFT];
		else if (cmp > 0)
			link = &node->child[RIGHT];
		else
			break;
		*parent = node;
	}
	return link;
}

@* Insertion.
@<exported functions@>+=
extern void
rb_ins(struct rb_node *, struct rb_node *,
		struct rb_node **, struct rb_node **);

@ Adding a node to the red-black tree is similar to the ordinary BST insertion.
Extra care is taken to maintain the invariants.
@c

void
rb_ins(struct rb_node *node, struct rb_node *parent,@|
		struct rb_node **link, struct rb_node **root)
{
	@<add new node to the tree@>@;
	@<maintain invariants after insertion@>@;
}

@ When adding a new node, the new node is colored red.
This way, I will not introduce black violations.
Each path from the root to |NULL| still has the same number of black nodes.
@<add new node...@>=
*link = node; /* newly inserted node is red */
node->child[LEFT] = node->child[RIGHT] = NULL;
node->parent_color = (uintptr_t) parent | RED_MASK;

@ Since I've inserted a red node, a red violation may occur.
That is, its parent is also red, violating the invariant that
``every red node has only black children.''

Or the newly inserted node can be the root, violating the
invariant that the root must be black.

I'm going to fix these problems.  
A loop is used here because the red violation may get
propagated up the tree (in |@<insertion case 1@>|),
so I have to fix it again (and again\dots)
until there's no red violation or I reached the root.

@<maintain invariants after insert...@>=
for (;;) {
	struct rb_node *sibling, *grandparent;
	int dir, lastdir;

	@<if |node| is root, update root and |break|@>@;
	@<move up one level, |break| if met a black node@>@;
	@<calculate |dir|, |sibling| and |link|@>@;
	if (IS_RED(sibling)) {
		@<insertion case 1@>@;
	} else if (dir == lastdir) {
		@<insertion case 2@>@;
	} else {
		@<insertion case 3@>@;
	}
}

@ If the ``troublemaker''%
\footnote*{the ``troublemaker'' can be the newly inserted (red) node,
but it can also be a red node made by a color flip,
possibly causing another red violation.}
has no parent (i.e., it's the root),
it's trivial to fix---simply change it to black.
It will (and is the only way to) increase the number of black nodes
in every path.

@<if |node| is root, update...@>=
if (parent == NULL) { /* |node| is root */
	SET_BLK(node);
	*root = node;
	break;
}

@ If the ``troublemaker'' is not root,
I will now move up my cursor by one level.
For example, in the figure below, $Y$ is the troublemaker.
Before I move up, |node| points to |Y| and |parent| points to |X|.
$$\figure{rbtree.8}$$
After moving up, |node| points to |X| and |parent| points to |P|.

Node that at most one of $X$ and $P$ is red,
otherwise I have broken the invariants even before the insertion!
(Then it's time to use the debugging facilities\dots)

@<move up one level...@>=
lastdir = parent->child[LEFT] == node ? LEFT : RIGHT;
/* direction from |X| to |Y| */
node = parent;
parent = PARENT(node);
assert(IS_RED(node)+IS_RED(parent)<2);
if (!IS_RED(node))
	break; /* No red violation! */

@ After moving up, if $X$ is black, there's no red violation,
and the maintenance terminates.

Otherwise, there is a red violation, and I need more
information to determine what to do next.

\item{1.} $S$ is $X$'s sibling (i.e., $P$'s other child).

\item{2.} I need to find the pointer pointing to $P$,
because I may have to do tree rotations.
|link| is the pointer to that pointer (because tree rotations make changes to
the pointer).

\item{3.} |dir| and |lastdir| are described in the code.
They are useful to determine what rotation to perform.

@<calculate |dir|...@>=
assert(parent != NULL);
grandparent = PARENT(parent);
if (grandparent == NULL) {
	link = root;
} else if (grandparent->child[LEFT] == parent) {
	link = &grandparent->child[LEFT];
} else {
	link = &grandparent->child[RIGHT];
}
dir = parent->child[LEFT] == node ? LEFT : RIGHT;
sibling = parent->child[!dir];
/* direction from |P| to |X| */

@ Case 1.  Sibling is red.  In this case, do a color flip,
i.e., change the color of the current node and its sibling
from red to black, and then change the parent from black
to red.
$$\figure{rbtree.8}
\quad\overrightarrow{color flip}\hskip.5em % weird
\figure{rbtree.9}$$
It doesn't matter if $Y$ is the left or right child of $X$,
the figure only shows one of the possibilities.
(Nodes with thicker circles are red.)

Keep an eye on each case for why the maintenance operation
(in this case, a color flip) does not introduce black violations.
One way to check this is to count the number of black nodes
from the root of this subtree to the top of each ``$\triangle$''
in the figure.  (The triangles can be either |NULL| or a subtree.)
The count should remain the same before and after the operation,
and with some thinking (please), it should be clear the black count
in every path is not affected.

This may introduce a new red violation,
but the situation can be handled similarly:
just set |node| and |parent| for the new troublemaker
(in this case, $P$), and let the loop continue.

@<insertion case 1@>=
SET_BLK(sibling);
SET_BLK(node);
SET_RED(parent);
@<prepare for the next iteration@>@;

@ @<prepare for the next iteration@>=
node = parent;
parent = grandparent;

@ Case 2.  Sibling is black, and the red child is an outer child.
This is fixed by a single rotation.
$$\figure{rbtree.10}\quad
\overrightarrow{single rotation}
\quad\figure{rbtree.11}$$
Note that after the rotation, I need to set $X$ to black, and $P$ to red.
Fortunately my rotation routines have done this for me.

After the rotation, the root of the subtree is black, so no more
red violation can be introduced.  The loop terminates.

@<insertion case 2@>=
single_rotation(link, !dir);
break;

@ Case 3.  Sibling is black, and the red child is an inner child.
This is not quite different from case~2, except that a double rotation
is needed.  (Draw a picture to see why a single rotation does not solve
the problem.)
$$\figure{rbtree.12}
\quad\overrightarrow{double rotation}\hskip.5em % weird
\figure{rbtree.13}$$

@<insertion case 3@>=
double_rotation(link, !dir);
break;


@* Deletion.
Deletion in a red-black tree is more complicated than insertion.

As in the ordinary BST, deleting a node with two non-|NULL| children
is complicated.
The first thing I'll consider is how to delete a {\it semi-leaf node}.
A semi-leaf node is one that at least one child of it is |NULL|.

The function |delete_semileaf| takes many arguments,
some can be easily derived from the others.
Why passing all of them?
Answer: this is a subroutine to be called by the real deletion routine,
in which all these arguments are hopefully already calculated,
so I don't want a re-calculation.

@c
static void delete_semileaf(
	struct rb_node *node, struct rb_node *parent,@| struct rb_node *child,
	struct rb_node **link, struct rb_node **root)
{
	@<attach the other child to the parent@>@;
	@<maintain invariants after deletion@>@;
}

@ Attaching the other child involves two operations:
1) update the child pointer in the parent;
2) update the child's parent pointer,
but only if the child is non-|NULL|.

The second case is only possible when |node| is black and its |!dir|-child
is red.  Otherwise the other child must be |NULL|.

@<attach the other child...@>=
*link = child;
if (child != NULL) {
	assert(IS_RED(child));
	SET_PARENT(child, parent);
}

@ When |node| is red, the deletion is trivial.
Because the invariants are not violated,
no maintenance action is required.

@<maintain invariants after deletion@>+=
if (IS_RED(node))
	return;

@ If a black node is deleted, there is a black violation (unless the node
is the root).

Here is the tricky thing: why do I set |node| to |child|
(the child that has been attached to the parent,
which is possibly |NULL|!) now?
Answer: inside the loop in the next section,
|node| will not be de\-referenced, but
it must be consistent with what is recorded in its parent's
|child| pointers.
(Why don't I set it earlier? See what the previous section does.)

Moreover, if the attached child is red, I can change it to black,
so that the invariants are restored, and I can terminate the maintenance
process.

@<maintain invariants after deletion@>=
node = child;
if (IS_RED(node)) {
	SET_BLK(node);
	return;
}

@ Although I'm deleting a semi-leaf node, I can generalize the problem:
If I have a subtree (the ``troublemaker'')
such that the black count in every path in the subtree
is one less than the ``correct value'',
how do I restructure the tree to restore the invariants?
$$\figure{rbtree.14}$$
In the above figure, $X$-subtree is the troublemaker.%
\footnote*{$X$ can be |NULL| that used to be the now-deleted node,
or it can be a subtree due to |@<deletion case 5@>|.}
$P$ is $X$'s parent, and $S$ is $X$'s sibling.
$A$ and $B$ are the {\it outer nephew\/} and
the {\it inner nephew\/}, respectively.

The action to take depends on the color of
the parent, of the sibling, and of the nephews (children of the sibling).
After studying them case by case, I found that there are 5 distinct
actions (not accounting for symmetic ones!).

@<maintain invariants after deletion@>=
for (;;) {
	struct rb_node *sibling, *grandparent;
	int dir;

	assert(!IS_RED(node));
	if (parent == NULL)
		break; /* no problem if I reached root */
	@<calculate |dir|, |sibling|...@>@;
	if (IS_RED(sibling)) {
		@<deletion case 1@>@;
	} /* no |else| here, as case 1 is reduced to the following ones */
	if (IS_RED(sibling->child[!dir])) { /* outer nephew */
		@<deletion case 2@>@;
	} else if (IS_RED(sibling->child[dir])) { /* inner nephew */
		@<deletion case 3@>@;
	} else if (IS_RED(parent)) {
		@<deletion case 4@>@;
	} else {
		@<deletion case 5@>@;
	}
}

@ Case 1.  The sibling is red.
A single rotation will tranform the subtree
so that the sibling will be black.
In fact, the sibling is black in all other cases.
So I can reduce this case to other cases.
(That's why it's called a {\it case reduction}.)
This is quite magical at first glance.
$$\figure{rbtree.15}\quad
\overrightarrow{single rotation}
\quad\figure{rbtree.16}$$
After the rotation, I proceed to look for one of the other cases.
But I must be careful to update the pointers:
now, the grandparent is $S$, the sibling is $B$,
and |link| should points to $S$'s |dir|-child pointer.

@<deletion case 1@>=
single_rotation(link, dir);
grandparent = sibling;
link = &sibling->child[dir];
sibling = parent->child[!dir];

@ Case 2.  The outer nephew is red.
I'll first change the it to black, then perform a single rotation.
This fixes the problem, because the black count for paths in $X$'s subtree
has increased by 1, while for other paths it has not changed.
$$\figure{rbtree.17}\quad
\overrightarrow{single rotation}
\quad\figure{rbtree.18}$$
After the process, since the black violation in
$X$'s subtree has been resolved, I can terminate the maintenance process.

@<deletion case 2@>=
single_rotation(link, dir);
SET_BLK(sibling->child[!dir]);
break;

@ Case 3.  The outer nephew is black, and the inner nephew is red.
Sounds like a double rotation is required.
$$\figure{rbtree.19}\quad
\overrightarrow{double rotation}\hskip.5em % visual weirdness
\figure{rbtree.20}$$
@<deletion case 3@>=
double_rotation(link, dir);
SET_BLK(sibling);
break;

@ Case 4.  The sibling and both nephews are black, and the parent is red.
In this case, change the parent to black and the sibling to red.
$$\figure{rbtree.21}\quad
\longrightarrow\hskip.5em % visual weirdness
\figure{rbtree.22}$$
@<deletion case 4@>=
SET_RED(sibling);
SET_BLK(parent);
break;

@ Case 5.  The sibling and both nephews are black,
and the parent is also black.

This case is put at the very last for a good reason:
I don't have any red node to be used in some way so that
the missing black count in $X$-subtree can be compensated.

It turns out that I can handle it the other way:
change the sibling to red,
so the black count in $S$-subtree all decrease by 1!
$$\figure{rbtree.23}\quad
\longrightarrow\hskip.5em % visual weirdness
\figure{rbtree.22}$$
The idea is, now every path in $P$-subtree has the same black count,
but it's one less the amount it should be,
in order to align with the invariants.
So, $P$ is the new ``troublemaker''.

@<deletion case 5@>=
SET_RED(sibling);
@<prepare for the next iteration@>@;


@ Now the general case: deletion of an arbitrary node.
The only information is the pointer to the node to be deleted,
and the pointer to the pointer to the node
(in case of the node being changed during deletion).

@<exported functions@>+=
extern void
rb_del(struct rb_node *, struct rb_node **);

@ @c
void rb_del(struct rb_node *node, struct rb_node **root)
{
	struct rb_node *parent, **link;

	parent = PARENT(node);
	if (parent == NULL)
		link = root;
	else if (parent->child[LEFT] == node)
		link = &parent->child[LEFT];
	else
		link = &parent->child[RIGHT];

	if (node->child[LEFT] == NULL) {
		delete_semileaf(node, parent, node->child[RIGHT], link, root);
	} else if (node->child[RIGHT] == NULL) {
		delete_semileaf(node, parent, node->child[LEFT], link, root);
	} else {
		@<deletion of a non-semileaf node@>@;
	}
	node->parent_color = 0;
	node->child[LEFT] = node->child[RIGHT] = NULL; /* nice to be clean */
}

@ In order to delete a node that is not a semi-leaf, the standard trick is
to replace the node with its predecessor (which must be a semi-leaf).
Then, the problem is reduced to how to remove a semi-leaf.

@<deletion of a non-semileaf node@>=
struct rb_node *vnode, *vleft, **vlink;

assert(node->child[LEFT] != NULL);
vlink = &node->child[LEFT];
vnode = node->child[LEFT];
if (vnode->child[RIGHT] == NULL) {
	@<deletion with victim, case 1@>@;
} else {
	do {
		vlink = &vnode->child[RIGHT];
		vnode = vnode->child[RIGHT];
	} while (vnode->child[RIGHT] != NULL);
	@<deletion with victim, case 2@>@;
}

@ @<deletion with victim, case 1@>=
vleft = vnode->child[LEFT];
*link = vnode;
vnode->child[RIGHT] = node->child[RIGHT];
SET_PARENT(vnode->child[RIGHT], vnode);
@<swap |parent_color| of |node| and |vnode|@>@;
delete_semileaf(node, vnode, vleft, &vnode->child[LEFT], root);

@ @<deletion with victim, case 2@>=
vleft = vnode->child[LEFT];
*link = vnode;
vnode->child[LEFT] = node->child[LEFT];
SET_PARENT(vnode->child[LEFT], vnode);
vnode->child[RIGHT] = node->child[RIGHT];
SET_PARENT(vnode->child[RIGHT], vnode);
@<swap |parent_color|...@>@;
delete_semileaf(node, PARENT(node), vleft, vlink, root);

@ @<swap |parent_color|...@>=
{
	uintptr_t t;
	t = vnode->parent_color;
	vnode->parent_color = node->parent_color;
	node->parent_color = t;
}
@* Index.

