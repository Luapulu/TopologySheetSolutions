<TeXmacs|2.1.1>

<style|generic>

<\body>
  <section|Characterisation of Metric Continuity>

  <\definition>
    <dueto|Open set in a metric space>A set <math|U\<subseteq\>X> in a metric
    space <math|<around*|(|X,d|)>> is open if <math|U> contains some
    <math|\<varepsilon\>>-ball <math|B<rsub|\<varepsilon\>><around*|(|x|)>>
    centered at every <math|x\<in\>U>. In other words
    <math|\<forall\>x\<in\>U,\<exists\>\<varepsilon\>\<gtr\>0:B<rsub|\<varepsilon\>><around*|(|x|)>\<subseteq\>U>.
  </definition>

  <\definition>
    <dueto|<math|\<varepsilon\>>-Ball>Let <math|<around*|(|X,d|)>> be a
    metric space. An <math|\<varepsilon\>>-Ball centered at <math|x\<in\>X>
    is the set

    <\equation*>
      B<rsub|\<varepsilon\>><around*|(|x|)>=<around*|{|y\<in\>X:d<around*|(|x,y|)>\<less\>\<varepsilon\>|}>
    </equation*>
  </definition>

  <\proposition>
    Let <math|X,Y> be metric spaces and <math|f:X\<rightarrow\>Y>, a map. The
    following statements are equivalent.

    <\enumerate-alpha>
      <item>For all <math|x\<in\>X>, there exists <math|\<delta\>\<gtr\>0>
      such that <math|f<around*|(|B<rsub|\<delta\>><around*|(|x|)>|)>\<subseteq\>B<rsub|\<varepsilon\>><around*|(|f<around*|(|x|)>|)>>
      for arbitrary <math|\<varepsilon\>\<gtr\>0>.

      <item>For all <math|y\<in\>Y>, the preimage
      <math|f<rsup|-1><around*|(|B<rsub|\<varepsilon\>><around*|(|y|)>|)>\<subseteq\>X>
      is open for arbitrary <math|\<varepsilon\>\<gtr\>0>.

      <item>The preimage <math|f<rsup|-1><around*|(|U|)>\<subseteq\>X> is
      open for arbitrary open <math|U\<subseteq\>Y>.

      <item>If the sequence <math|<around*|(|x<rsub|n>\<in\>X|)><rsub|n\<in\>\<bbb-N\>>>
      converges to <math|x\<in\>X>, then <math|<around*|(|f<around*|(|x<rsub|n>|)>\<in\>X|)><rsub|n\<in\>\<bbb-N\>>>
      converges to <math|f<around*|(|x|)>\<in\>Y>.
    </enumerate-alpha>

    Note that we use the metric definition of open here.
  </proposition>

  <\proof>
    <strong|<math|b\<Rightarrow\>a>>

    Let <math|x\<in\>X> and <math|B<rsub|\<varepsilon\>><around*|(|f<around*|(|x|)>|)>>
    be some <math|\<varepsilon\>>-ball centered at <math|f<around*|(|x|)>>.
    By our assumption, the preimage <math|f<rsup|-1><around*|(|B<rsub|\<varepsilon\>><around*|(|f<around*|(|x|)>|)>|)>>
    is open. In particular, this implies that there exists a
    <math|\<delta\>>-ball centered at <math|x>, such that
    <math|B<rsub|\<delta\>><around*|(|x|)>\<subseteq\>f<rsup|-1><around*|(|B<rsub|\<varepsilon\>><around*|(|f<around*|(|x|)>|)>|)>>,
    which implies <math|f<around*|(|B<rsub|\<delta\>><around*|(|x|)>|)>\<subseteq\>B<rsub|\<varepsilon\>><around*|(|f<around*|(|x|)>|)>>.

    <strong|<math|a\<Rightarrow\>c>>

    Let <math|U\<subseteq\>Y> be some open set in <math|Y> and let
    <math|x\<in\>f<rsup|-1><around*|(|U|)>>. Then, by <em|a>, there exists a
    <math|\<delta\>\<gtr\>0>, such that <math|f<around*|(|B<rsub|\<delta\>><around*|(|x|)>|)>\<subseteq\>B<rsub|\<varepsilon\>><around*|(|f<around*|(|x|)>|)>>
    for arbitrary <math|\<varepsilon\>\<gtr\>0>. For sufficiently small
    <math|\<varepsilon\>>, <math|B<rsub|\<varepsilon\>><around*|(|f<around*|(|x|)>|)>\<subseteq\>U>,
    since <math|U> is open and <math|f<around*|(|x|)>\<in\>U>. Therefore,
    <math|f<around*|(|B<rsub|\<delta\>><around*|(|x|)>|)>\<subseteq\>B<rsub|\<varepsilon\>><around*|(|f<around*|(|x|)>|)>\<subseteq\>U>,
    which means <math|B<rsub|\<delta\>><around*|(|x|)>\<subseteq\>f<rsup|-1><around*|(|U|)>>.

    <strong|<math|c\<Rightarrow\>b>>

    If <math|f<rsup|-1><around*|(|U|)>> is open for an arbitrary set
    <math|U\<subseteq\>Y>, it is also open for the case
    <math|U=B<rsub|\<varepsilon\>><around*|(|y|)>>.

    <strong|<math|a\<Rightarrow\>d>>

    Let <math|<around*|(|x<rsub|n>\<in\>X|)><rsub|n\<in\>\<bbb-N\>>> be a
    sequence which converges to <math|x\<in\>X>. Then,
    <math|<around*|{|x<rsub|n>\<in\>X:n\<gtr\>N|}>> is contained in any
    <math|\<delta\>>-ball <math|B<rsub|\<delta\>><around*|(|x|)>> for some
    sufficiently large <math|N>. By <em|a>, this means we may find a
    <math|\<delta\>\<gtr\>0>, such that <math|<around*|{|f<around*|(|x<rsub|n>|)>\<in\>Y:n\<gtr\>N|}>\<subseteq\>f<around*|(|B<rsub|\<delta\>><around*|(|x|)>|)>\<subseteq\>B<rsub|\<varepsilon\>><around*|(|f<around*|(|x|)>|)>>
    for any <math|\<varepsilon\>\<gtr\>0>. In other words, for any
    <math|\<varepsilon\>\<gtr\>0>, <math|d<around*|(|f<around*|(|x<rsub|n>|)>,f<around*|(|x|)>|)>\<less\>\<varepsilon\>>
    for all <math|n\<gtr\>N>, which implies
    <math|<around*|(|f<around*|(|x<rsub|n>|)>\<in\>X|)><rsub|n\<in\>\<bbb-N\>>>
    converges to <math|f<around*|(|x|)>\<in\>Y>.

    <strong|<math|\<neg\>a\<Rightarrowlim\>\<neg\>d>>

    Let us assume that for some <math|x\<in\>X> and some
    <math|\<varepsilon\>>-ball <math|B<rsub|\<varepsilon\>><around*|(|f<around*|(|x|)>|)>>,
    there exists no <math|\<delta\>\<gtr\>0> such that
    <math|f<around*|(|B<rsub|\<delta\>><around*|(|x|)>|)>\<subseteq\>B<rsub|\<varepsilon\>><around*|(|f<around*|(|x|)>|)>>.
    Since <math|f<around*|(|B<rsub|\<delta\>><around*|(|x|)>|)>\<nsubseteq\>B<rsub|\<varepsilon\>><around*|(|f<around*|(|x|)>|)>>
    for all <math|\<delta\>\<gtr\>0>, for all upper bounds
    <math|d\<gtr\>d<around*|(|x,z|)>>, there exists at least some
    <math|z<rsub|d>\<in\>X>, such that <math|d<around*|(|f<around*|(|x|)>,f<around*|(|z<rsub|d>|)>|)>\<geqslant\>\<varepsilon\>>.
    Now we define the sequence <math|<around*|(|z<rsub|d<around*|(|n|)>>\<in\>X|)><rsub|n\<in\>\<bbb-N\>>>,
    where the upper bound <math|d<around*|(|n|)>> is a monotonically
    decreasing function of <math|n>. This sequence converges to <math|x>, but
    <math|<around*|(|f<around*|(|z<rsub|d<around*|(|n|)>>|)>\<in\>Y|)><rsub|n\<in\>\<bbb-N\>>>
    does not converge to <math|f<around*|(|x|)>> since
    <math|d<around*|(|f<around*|(|x|)>,f<around*|(|z<rsub|d<around*|(|n|)>>|)>|)>\<geqslant\>\<varepsilon\>>
    for some <math|\<varepsilon\>> and for all <math|d>.
  </proof>

  <section|Neighbourhoods>

  <\lemma>
    Let <math|X> be a topological space and let <math|U<rsub|i>> be open sets
    with <math|1\<leqslant\>i\<leqslant\>N> for some <math|N>. The
    intersection of all <math|U<rsub|i>> is open.
  </lemma>

  <\proof>
    Let <math|V<rsub|n>> be the intersection of all <math|U<rsub|i>> with
    <math|i\<leqslant\>n>. <math|V<rsub|1>=U<rsub|1>> is open. If
    <math|V<rsub|k>> is open, the intersection of <math|V<rsub|k>> and
    <math|U<rsub|k+1>> is open. Therefore, <math|V<rsub|k+1>> is open. By
    induction, <math|V<rsub|N>> is open and so the intersection of all
    <math|U<rsub|i>> is open.
  </proof>

  <\proposition>
    Let <math|V<rsub|1>,\<ldots\>,V<rsub|n>> be a finite collection of
    neighbourhoods of <math|x\<in\>X>. Their intersection is also a
    neighborhood of <math|x\<in\>X>.
  </proposition>

  <\proof>
    Each neighbourhood <math|V<rsub|i>> contains an open set
    <math|U<rsub|i>>, which contains <math|x>. The intersection <math|U> of
    all <math|U<rsub|i>> is open and must be contained in the intersection
    <math|V> of all <math|V<rsub|i>>. <math|U> and <math|V> must also contain
    <math|x>. <math|Thus,V> is also a neighbourhood.
  </proof>

  <\proposition>
    Let <math|X> be a topological space. If <math|U> is a neighbourhood of
    <math|x\<in\>X> then <math|U> is the neighbourhood of all <math|y\<in\>V>
    for some neighbourhood <math|V> of <math|x>.
  </proposition>

  <\proof>
    <math|U> contains an open set <math|V>, which contains <math|x>. <math|V>
    is a neighbourhood for all elements in <math|V>, since <math|V> contains
    an open set <math|V>, which contains all elements in <math|V>.
  </proof>

  <\proposition>
    A subset <math|U\<subseteq\>X> is open if and only if it is a
    neighbourhood of all its points
  </proposition>

  <\proof>
    If <math|U> is open it contains an open set <math|U> which also contains
    every element of <math|U>. Therefore <math|U> is a neighbourhood of all
    its points.

    For the reverse, let V be a neighborhood of all its elements. For every
    <math|x\<in\>V> we have an open set <math|U<rsub|x>> such that
    <math|x\<in\>U<rsub|x>\<subseteq\>V>. Consider now the set
    <math|W=<below|<big|cup>|x\<in\>V> U<rsub|x>>. <math|W\<subseteq\>V>
    because all the consitutent <math|U<rsub|x>> are subsets of <math|V>. On
    the other hand <math|V\<subseteq\>W>, since every <math|x\<in\>V> is an
    element of <math|U<rsub|x>\<subseteq\>W>. So, <math|W=V> and since
    <math|W> is a union of open sets, <math|W> itself is open, which means
    <math|V> is open.
  </proof>

  <section|Maps Between Topological Spaces>

  <subsection|Bijective Maps>

  In this subsection, let <math|X> and <math|Y> be topological spaces and
  <math|f:X\<rightarrow\>Y> a bijective map.

  <\proposition>
    <label|preimage-inverse>The preimage of a set <math|U> under <math|f> is
    equal to the inverse of <math|f> applied to <math|U>.
  </proposition>

  <\proof>
    Let the preimage of <math|U> be the set
    <math|A=<around*|{|x\<in\>X:f<around*|(|x|)>\<in\>U|}>> and the inverse
    applied to <math|U> be the set <math|B=<around*|{|f<rsup|-1><around*|(|y|)>:y\<in\>U|}>>.
    If <math|x\<in\>A> is an element of the preimage,
    <math|f<around*|(|x|)>\<in\>U> is an element of <math|U>. Since <math|f>
    is one-to-one, <math|x=f<rsup|-1><around*|(|y|)>> for
    <math|y=f<around*|(|x|)>\<in\>U> and so <math|x> is also an element of
    <math|B>. If <math|x> is now taken to be an element of <math|B>, we know
    that <math|x=f<rsup|-1><around*|(|y|)>> for some <math|y\<in\>U>. Because
    <math|f> is injective, there is only one such pair
    <math|<around*|(|x,y|)>> with <math|x=f<rsup|-1><around*|(|y|)>> and
    because <math|f> is surjective, the unique <math|x> must be in the domain
    if <math|y> is in the codomain. Therefore <math|x\<in\>X> and
    <math|f<around*|(|x|)>\<in\>U>, meaning <math|x> is also an element of
    <math|A> if it is an elemnt of <math|B>.
  </proof>

  <\proposition>
    <math|f> is a homeomorphism if and only if <math|f:X\<rightarrow\>Y> is
    open
  </proposition>

  <\proof>
    Notice that <math|f<around*|(|U|)>> is the preimage of <math|U> under the
    map <math|f<rsup|-1>>, since

    <\equation*>
      f<around*|(|U|)>=<around*|{|f<around*|(|x|)>:x\<in\>U|}>=<around*|{|<around*|(|f<rsup|-1>|)><rsup|-1><around*|(|x|)>:x\<in\>U|}>=<around*|{|y\<in\>Y:f<rsup|-1><around*|(|y|)>\<in\>U|}>
    </equation*>

    where the last equality used proposition <reference|preimage-inverse> to
    equate the inverse applied to a set with the preimage of <math|U> under
    the map <math|f<rsup|-1>>. Therefore, if <math|f> is open all preimages
    of open sets under <math|f<rsup|-1>> are open, meaning <math|f<rsup|-1>>
    is continuous, which implies <math|f> is a homeomorphism. Conversely, if
    <math|f> is a homeomorphism, preimages of open sets under
    <math|f<rsup|-1>> are open, which is equivalent to saying <math|f> maps
    open sets to open sets and so <math|f> is open.
  </proof>

  <\lemma>
    <label|compliment-to-compliment><math|f<around*|(|X\<setminus\>U|)>=Y\<setminus\>f<around*|(|U|)>>
    for any subset <math|U\<subseteq\>X>.
  </lemma>

  <\proof>
    Any point <math|y\<in\>f<around*|(|X\<setminus\>U|)>> must be in <math|Y>
    and cannot be in <math|f<around*|(|U|)>>. If <math|y> were an element of
    <math|f<around*|(|U|)>>, too, there would be some point in <math|U> and
    some point in <math|X\<setminus\>U> which both map to <math|y>. However,
    this contradicts <math|f> being an injective function. Therefore <math|y>
    is an element of <math|Y\<setminus\>f<around*|(|U|)>>.

    On the other hand, any point <math|y\<in\>Y\<setminus\>f<around*|(|U|)>>
    must be
  </proof>

  <\proposition>
    <math|f> is open if and only if <math|f> is closed
  </proposition>

  <\proof>
    Let <math|f> be open (or closed for the converse) and
    <math|U\<subseteq\>X> be an open (closed) set. Then
    <math|f<around*|(|U|)>\<subseteq\>Y> is open (closed) and the compliment
    <math|Y\<setminus\>f<around*|(|U|)>> is closed (open). as shown in lemma
    <reference|compliment-to-compliment>,
    <math|f<around*|(|X\<setminus\>U|)>=Y\<setminus\>f<around*|(|U|)>>, so
    <math|f> also maps the closed (open) set <math|X\<setminus\>U> to the
    closed (open) set <math|Y\<setminus\>f<around*|(|U|)>>. Because every
    closed (open) set is the compliment of some open (closed) set, the map
    <math|f> is closed (open).
  </proof>

  <subsection|Generic Maps>

  In this subsection, let <math|X> and <math|Y> be topological spaces and
  <math|f:X\<rightarrow\>Y> a map between them.

  <\proposition>
    Arbitrary <math|f> are continuous if and only if the topology on <math|X>
    is discrete or the topology on <math|Y> is coarse.
  </proposition>

  <\proof>
    If the topology on <math|X> is discrete any subset of the domain is open,
    in particular every preimage is open. Therefore, <math|f> is continuous.

    If the topology on <math|Y> is coarse, we need only look at preimages of
    <math|\<varnothing\>> and <math|Y>, since those are the only open sets.
    The preimage of <math|\<varnothing\>> is <math|\<varnothing\>>, which is
    open; the preimage of <math|Y> is <math|X>, which is open, since all
    elements in <math|X> map into <math|Y>.

    For the converse, suppose all maps <math|f:X\<rightarrow\>Y> are
    continuous, but the topology on <math|X> is not discrete and the topology
    on <math|Y> is not coarse. Then, there exists a subset
    <math|U\<subseteq\>X> which is not open and an open subset
    <math|V\<subset\>Y> different from <math|\<varnothing\>> and <math|Y>. If
    we pick <math|f>, such that <math|f<around*|(|U|)>=V>, the preimage of
    the open set <math|V> would be the set <math|U>, which is not open.
    Therefore, we have a contradiction since and <math|f> ought to be
    continuous.
  </proof>

  <\proposition>
    Let <math|\<cal-S\>> be a subbasis of the topology on <math|Y>. The, the
    map <math|f:X\<rightarrow\>Y> is continuous if and only if the preimage
    <math|f<rsup|-1><around*|(|U|)>> is open in <math|X> for any
    <math|U\<in\>\<cal-S\>>.
  </proposition>

  <\proof>
    If the map <math|f> is continuous, preimages of any open sets in <math|Y>
    are open. In particular, since elements of the subbasis are themselves
    open, the preimages <math|f<rsup|-1><around*|(|U|)>> for
    <math|U\<in\>\<cal-S\>> must be open.

    For the converse, let preimages of sets in the subbasis be open. Since
    any set <math|U\<subseteq\>Y> may be expressed as a union of finite
    intersections of sets in <math|\<cal-S\>>, we have

    <\eqnarray*>
      <tformat|<table|<row|<cell|f<rsup|-1><around*|(|U|)>>|<cell|=>|<cell|<around*|{|x\<in\>X:f<around*|(|x|)>\<in\>U|}>>>|<row|<cell|>|<cell|=>|<cell|<around*|{|x\<in\>X:f<around*|(|x|)>\<in\><big|cup><around*|{|<big|cap>V<rsub|i>:V<rsub|i>\<in\>\<cal-S\>|}>|}>>>|<row|<cell|>|<cell|=>|<cell|<big|cup><around*|{|x\<in\>X:f<around*|(|x|)>\<in\><big|cap>V<rsub|i>|}>>>|<row|<cell|>|<cell|=>|<cell|<big|cup><around*|{|<big|cap><around*|{|x\<in\>X:f<around*|(|x|)>\<in\>V<rsub|i>|}>|}>>>|<row|<cell|>|<cell|=>|<cell|<big|cup><around*|{|<big|cap>f<rsup|-1><around*|(|V<rsub|i>|)>|}>>>>>
    </eqnarray*>

    By our assumption, preimages of the subbasis elements <math|V<rsub|i>>
    are open and because a union of finite intersections of open sets must be
    open, <math|f<rsup|-1><around*|(|U|)>> is open, which implies <math|f> is
    continuous.
  </proof>

  \;

  <section|Closure, Interior, Boundary>

  <\proposition>
    The set <math|A<rsup|0>> is the maximal open set contained in A.
  </proposition>

  <\proof>
    Choose a point <math|x\<nin\>A<rsup|0>>. This means A is not a
    neighborhood of x, so there is no open set <math|U\<subseteq\>A> with
    <math|x\<in\>U>.

    \<rightarrow\> <math|A\<setminus\>A<rsup|0>> contains no open sets (The
    union of all open sets in <math|A> is contained in <math|A<rsup|0>>)

    Show that <math|A<rsup|0>> is open:

    Choose a point <math|x\<in\>A<rsup|0>> \<rightarrow\>
    <math|A\<in\>N<rsub|x>>

    \<rightarrow\> <math|x\<in\>U\<in\>O> and <math|U\<subseteq\>A>

    Each point <math|y> in <math|U> is also contained in <math|A<rsup|0>>,
    since an open set is a neighborhood of all its points.\ 

    \<rightarrow\>Every point in <math|A> is contained in an open set which
    is contained in <math|A<rsup|0>>. This makes <math|A<rsup|0>> open, since
    it can be expressed as the union of all these open sets.

    \;
  </proof>

  <\proposition>
    The set <math|<wide|A|\<bar\>>> is the minimal closed set containing A
  </proposition>

  <\proof>
    The given statement is equivalent to\ 

    <math|U<rsup|0>=X\<setminus\><wide|A|\<bar\>>> is the maximal open set
    not containing any elements of <math|A>. We see this by showing that
    <math|U<rsup|0> > is the interior of <math|U=X\<setminus\>A>, after which
    it follows directly from prop. 14.\ 

    Choose <math|x\<in\>U<rsup|0>>. Then we want to see that
    <math|U\<in\>N<rsub|x>>. Since <math|x> is not in
    <math|<wide|A|\<bar\>>>, we have by negating the definition of
    <math|<wide|A|\<bar\>>>:

    There exists a <math|V\<in\>N<rsub|x>> such that we have
    <math|V\<cap\>A=\<varnothing\>>. This means that for this
    <math|V\<subseteq\>U>. Therefore <math|U> is also a neighborhood of
    <math|x>.
  </proof>

  <\proposition>
    We have \<partial\><math|A=<wide|A|\<bar\>>\<cap\><wide|X\<setminus\>A|\<bar\>>.>
  </proposition>

  <\proof>
    \;

    <\itemize-dot>
      <item><math|\<subseteq\>:>

      Choose <math|x\<in\>\<partial\>A>. Therefore both
      <math|<around*|(|A,X\<setminus\>A|)>\<nin\>N<rsub|x>>. We want to show
      that <math|x> is both in the closure of <math|A> and
      <math|X\<setminus\>A>.\ 

      To be in <math|<wide|A|\<bar\>>>, we need that for any
      <math|V\<in\>N<rsub|x>>, <math|V\<cap\>A\<neq\>\<varnothing\>>. Since
      <math|X\<setminus\>A\<nin\>N<rsub|x>>, we see immediately that
      \ <math|V\<cap\>A\<neq\>\<varnothing\>>, as the inverse would imply
      <math|V\<subseteq\>X\<setminus\>A>.\ 

      Similarly, because <math|A\<nin\>N<rsub|x>> it follows that
      <math|V\<cap\>X\<setminus\>A\<neq\>\<varnothing\>>, which means that
      <math|x\<in\><wide|X\<setminus\>A|\<bar\>>>.

      <item><math|\<supseteq\>:>

      Choose <math|x\<in\>><math|<wide|A|\<bar\>>\<cap\><wide|X\<setminus\>A|\<bar\>>.>
      We want to show <math|x\<in\>\<partial\>A>, meaning
      <math|<around*|(|A,X\<setminus\>A|)>\<nin\>N<rsub|x>>.

      Since <math|x\<in\><wide|A|\<bar\>>>, for any <math|V\<in\>N<rsub|x>>,
      <math|V\<cap\>A\<neq\>\<varnothing\>>. Therefore
      <math|X\<setminus\>A\<nin\>N<rsub|x>>.\ 

      Since <math|x\<in\><wide|X\<setminus\>A|\<bar\>>>, for any
      <math|V\<in\>N<rsub|x>>, <math|V\<cap\>X\<setminus\>A\<neq\>\<varnothing\>>.
      Therefore <math|A\<nin\>N<rsub|x>>.
    </itemize-dot>
  </proof>

  <\proposition>
    We have <math|<wide|A|\<bar\>>=\<partial\>A\<cup\>A<rsup|0>>.
  </proposition>

  <\proof>
    <math|>

    <\itemize-dot>
      <item><math|\<subseteq\>:>

      Choose <math|x\<in\><wide|A|\<bar\>>>. Then for any
      <math|V\<in\>N<rsub|x>>, <math|V\<cap\>A\<neq\>\<varnothing\>>. If
      <math|A\<in\>N<rsub|x>>, it follows immediately that <math|x> is in
      <math|A<rsup|0>>. If <math|A\<nin\>N<rsub|x>>, then from
      <math|V\<cap\>A\<neq\>\<varnothing\>> it follows that also
      <math|X\<setminus\>A\<nin\>N<rsub|x>>. Therefore
      <math|x\<in\>\<partial\>A>.

      <item><math|\<supseteq\>:>

      Choose <math|x\<in\>\<partial\>A>. Because
      <math|X\<setminus\>A\<nin\>N<rsub|x>>, it follows immediately that for
      all <math|V\<in\>N<rsub|x>>, <math|V\<cap\>A\<neq\>\<varnothing\>> (as
      seen before).\ 

      Choose <math|x\<in\>A<rsup|0>>. From <math|A\<in\>N<rsub|x>>, we see
      immediately that <math|x\<in\>A>, from which it follows that for all
      <math|V\<in\>N<rsub|x>>, <math|V\<cap\>A\<neq\>\<varnothing\>>.
    </itemize-dot>
  </proof>

  \;
</body>

<initial|<\collection>
</collection>>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|?>>
    <associate|auto-2|<tuple|2|?>>
    <associate|auto-3|<tuple|3|?>>
    <associate|auto-4|<tuple|3.1|?>>
    <associate|auto-5|<tuple|3.2|?>>
    <associate|auto-6|<tuple|4|?>>
    <associate|compliment-to-compliment|<tuple|10|?>>
    <associate|preimage-inverse|<tuple|8|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Characterisation
      of Metric Continuity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Neighbourhoods>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Maps
      Between Topological Spaces> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3><vspace|0.5fn>

      <with|par-left|<quote|1tab>|3.1<space|2spc>Bijective Maps
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <with|par-left|<quote|1tab>|3.2<space|2spc>Generic Maps
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Closure,
      Interior, Boundary> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>