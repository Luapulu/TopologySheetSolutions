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

    For the reverse, let <math|U<rsub|i>> be some neighbourhood of all its
    elements. The intersection <math|U<rsub|i>\<cap\>U<rsub|j>> is a
    neighbourhood since <math|U<rsub|i>> and <math|U<rsub|j>> are both
    neighborhoods of some point in the intersection (using our previous
    result). A union <math|V> of <math|U<rsub|i>> is a neighbourhood of all
    its points, since we can find an open set contained in <math|V> that
    contains every point. Let <math|x\<in\>V>. <math|x> must also be an
    element of some <math|U<rsub|i>>. Therefore an open set exists in
    <math|U<rsub|i>\<subseteq\>V> which contains <math|x> and so <math|V> is
    a neighbourhood of all its points. If we define a neighborhood, such that
    <math|\<varnothing\>> is a neighborhood of all its points and we realise
    that since <math|X> is open, it is a neighbourhood of all its points, we
    can see that <math|U<rsub|i>> is in fact open.
  </proof>

  \;
</body>

<\initial>
  <\collection>
    <associate|page-medium|paper>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-2|<tuple|2|1>>
    <associate|auto-3|<tuple|3|2>>
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
    </associate>
  </collection>
</auxiliary>