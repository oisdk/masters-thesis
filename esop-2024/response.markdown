# Rebuttal

We would like to thank the reviewers for their time and their feedback.
The comments were thourough and constructive, and will be helpful in improving
the paper.
We were happy to see many positive comments, especially with regard to the
quality of presentation:

> I found the paper highly readable, and I found the proof
> search solution for the countdown problem quite fun.
>
> - Reviewer 4

We think that reviewer 1 offers a short and accurate summary:

> The submission presents a Cubical Agda library about finite sets, which will
> certainly be useful to many future formalisation projects. It includes valuable
> automated reasoning tools. Moreover the submission is pleasant and interesting
> to read.

This response will consist first of an outline of the changes we plan to make to
the paper to address the comments, then a response to points made in multiple
reviews, and finally detailed responses to each review in turn.

## Proposed Changes

- Our primary change will be to cut the paper down to fit it into the LNCS page
  limit of 25. 
  We plan to do this by mainly shortening the early sections of the paper, which
  exposit finiteness predicates and theorems that are now new to this paper.
  Instead of giving an in-depth explanation of these proofs we will keep the
  discussion high-level, pointing to the prior work where it exists, and putting
  more focus on the novel work like Theorems 2.7 and 3.4, and the predicate
  manifest enumerability.
  
  We have changed the formatting from acmart to LNCS and at present (without any
  editing) the page count stands at 30, so we think this change will be
  sufficient to get us under the 25-page limit.
 
- We will include the actual code of the formalisation as an artefact submission
  alongside the paper itself.
  We were not sure if we should submit the code with the original submission
  (since there was a separate artefact submission process), and we don't think
  it is possible to submit it in this rebuttal.
  
  The code itself is about 9000 lines, and is typechecked in Cubical Agda
  version 2.6.2 using the cubical library version 0.3.
  All theorems, lemmas, and definitions in the paper are included in the
  formalisation, and have been typechecked using the `--safe` flag.
  
- We will change the example slightly to demonstrate the use of computational
  univalence better, as described below.
  
- We will also address the more minor points made (corrections, typos, etc.),
  detailed below.

## Response to Points in Multiple Reviews

### Presentation of standard results in first half of paper

Some of the early parts of the paper present relatively well-known results about
finiteness.
From reviewer 3:

> there seems to be quite some overlap between this paper and a
> few other papers discussed in related work.

Reviewer 4:

> A substantial part of the paper reviews definitions and theorems from previous
> literature.

Firstly we feel it is important to point out that while some of the results
referred to here are not new, the setting and formalisation is.
The related work in question here (Firsov and Uustalu [2015] and Frumin,
Geuvers, Gondelman, and Weide [2018]) do not use cubical Agda, and as such their
proofs are not immediately transferable to our formalisation.
The first uses Agda with the K rule, which is incompatible with cubical Agda,
and makes some proofs (for instance the injectivity of Fin) simpler; the second
is formalised in Coq with HoTT and no computational univalence.

That said, as mentioned in the proposed changes above, we are happy to shorten
up the exposition of these results for the sake of space, replacing that
exposition with a pointer to some existing work.
Furthermore, wherever a lemma or theorem has been proven elsewhere we will
include an inline reference to that proof (reviewer 3 mentioned lemma 2.2 in
particular).

### Use of univalence, especially in the example

From reviewer 3:

> However, the countdown example doesn’t really demonstrate the aforementioned
> ability: the exhaustive search is performed on a type which is complex but still
> doesn’t involve functions, so I find the example somewhat unsatisfactory.

Reviewer 4:

> with the exception of the proof search library, but there it'd be nice too see
> more about how computational univalence is being used.

In order to better demonstrate computational univalence, we will change the
example slightly.
Recall that we used a list-based representation of permutations (`Perm 0 = ⊤;
Perm (n+1) = Fin (n+1) × Perm n`) over an isomorphism-based representation
(`Perm n = Fin n ⇔ Fin n`) for performance reasons.
We will provide a proof that these two representations are isomorphic, and
*transport* the efficient exhaustive search over the list-based rep to search
over the isomorphism-based one.
So the type of countdown solutions will now include a function (in the form of
the isomorphism), but will (via univalence) search over listed permutations.

## Detailed responses

What follows is a response to each review in detail.

--------------------------------------------------------------------------------
> # Review 1
> 
> ## Overall evaluation
> 
> 2: (strong accept (the paper must be accepted))
> The submission presents a Cubical Agda library about finite sets, which will
> certainly be useful to many future formalisation projects. It includes valuable
> automated reasoning tools. Moreover the submission is pleasant and interesting
> to read.
> 
> See attached file (pages 1-2) for more info, including a couple of very minor
> corrections that should be made before publication
> 
> ## Reviewer's Confidence
> 
> 4: (high)
> 
> ## Questions for authors
> 
> none
> 
> ## Detailed comments for authors
> 
> See attached file for quite a lot of comments and suggestions.
> 
> Section 3 contains a couple of corrections I feel are important.
> 
> The later sections contain suggestions, the author(s) should feel free to choose
> which they implement and which they ignore.
> 
> ## Attachment
> 
> https://easychair.org/conferences/review_attachment.cgi?rid=11211749&a=31781025&track=294214
> 
--------------------------------------------------------------------------------
> # Review 2
> 
> ## Overall evaluation
> 
> 0: (weak accept / borderline (the paper can be accepted))
> This paper presents a library developed in Cubical Agda (an extension of Agda
> with several Cubical type theory features). More concretely, it presents several
> definitions of finite types that are all equivalent classically, and it explains
> how they are not equivalent but still related in a constructive and homotopical
> setting. Besides formalising known results, the main new contributions are:
> 
> - Theorem 2.7 constructing an equivalence between any cardinally finite type of
>   size n with a total order and Fin(n).
> - Theorem 3.4 stating that the category of cardinally finite types is a
>   Pi-pretopos.
> 
> - A library for automated proofs of formulas build from quantifying on finite
>   types and decidable propositions.
> 
> The paper seems well written and the results strong. However I do not feel we
> have enough expertise to properly evaluate its merits/relevance.
> 
> ## Reviewer's Confidence
> 
> 2: (low)
> 
> ## Questions for authors
> 
> None
> 
> ## Detailed comments for authors
> 
> Please make sure to respect the margins, see lines 70 and 83 (page 2) and Fig.
> 2 (page 19).

Fixed.

> 
--------------------------------------------------------------------------------
> # Review 3
> 
> ## Overall evaluation
> 
> 0: (weak accept / borderline (the paper can be accepted))
> This paper explores, in Cubical Agda, several definitions of constructive
> finiteness, implications among them, and their properties, notably closure under
> Sigma and Pi. The paper then develops a larger example, where the countdown
> problem is solved by exhaustively searching through the space of candidate
> solutions, which can be shown to be finite and is therefore equipped with
> generic search procedures.
> 
> I think this kind of paper that catalogues definitions that the programmer needs
> in their toolbox is valuable service to the community, so I want to convince
> myself to accept this paper. The presentation is easy to follow in general (at
> least for a reader who’s comfortable with Agda), and the paper strives to
> provide motivations for most of the definitions and (brief) recaps of HoTT, so
> that the paper doesn’t look like just a catalogue. I feel positive about the
> paper, but eventually I still have difficulty fully convincing myself.
> 
> First of all, I’m not familiar with the literature about constructive
> finiteness, but there seems to be quite some overlap between this paper and a
> few other papers discussed in related work.

Indeed, there is significant overlap with the early part of the paper and other
work (though we would point to Frumin, D., Geuvers, H., Gondelman, L., van der
Weide, N.: Finite Sets in Homotopy Type Theory [2018] as the closest work).
The difference with our work is the new setting of cubical type theory, which is
what facilitates the novel theorems later on (theorem 2.7, 3.4, and the library
development as a whole).

However, in the interests of space, we are happy to cut down the exposition of
these early theorems and instead present them from a high level, with pointers
to their original proofs.

> For a specific example: Lemma 2.2 is
> already proved by Firsov and Uustalu [2014] as ‘lstbl2deq’ in their Section 3.1.
> I think lemmas/theorems already proved in previous work should be marked
> explicitly as such, or even just briefly summarised to save space (to fit the
> whole paper into 25 LNCS pages).

We will explicitly mark every theorem and lemma in the paper with a reference to
pre-existing work, if it exists.

> Without univalence or at least function extensionality, it’s probably much more
> problematic to deal with finiteness that involves higher-order/function types.

Indeed, it is not possible to prove functions with cardinality other than 0 are
finite without extensionality.

> Thanks to Cubical Agda, in this paper we can state and prove equivalences
> between higher-order types, and prove that some of the formulations of
> finiteness are closed under Pi, while still getting proofs of properties such as
> exhaustibility and omniscience to compute. Previous work seems to establish only
> simpler closure properties (e.g., under sums and products — I took a look at the
> papers by Firsov and Uustalu [2014] and Frumin [2018]). I suppose the ability to
> deal with (dependent) function types nicely is the main contribution of this
> paper that differentiates it from previous work — if that’s the case, the
> contribution needs to be stated and demonstrated more clearly.

We will emphasise this contribution more clearly in an update.

> However, the countdown example doesn’t really demonstrate the aforementioned
> ability: the exhaustive search is performed on a type which is complex but still
> doesn’t involve functions, so I find the example somewhat unsatisfactory.
> Also,
> while using a larger example is a good idea, in this case exhaustive search is
> not a good way to solve the countdown problem. 

While it is certainly not an efficient solution, semantically speaking the
essence of the countdown problem is one of constraint satisfaction, and 
proving or disproving that a system of constraints is satisfiable amounts to
making a judgement about the cardinality of the set of possible solutions.
That is *precisely* what our work does.
The question "does this countdown problem have a solution" is a question about
the cardinality of the type representing its solutions.
A constructive answer to that question is a precise enumeration of that type.

To be clear, we don't imagine people using the library to solve problems like
the countdown problem.
We think that the finiteness proofs and explanations are useful for other
formalisation efforts

> The example is more like a fun
> exercise but doesn’t make a lot of sense by itself. This kind of example is not
> entirely appealing, but on the other hand it’s kind of acceptable: there’s a
> library that seems useful here and there, but the actual applications may not be
> so interesting, so for presentation purposes it makes sense to use a larger but
> not necessarily practical example to show how to use the library.

> If it’s not
> easy to extend the countdown example to cover function types, I suppose it’s
> fine to fill the gap with some practical (but maybe not-so-interesting)
> examples.

We can extend the countdown example to include functions, as described above.

> As for the more theoretical part of the paper: Theorem 2.7 is claimed to be new
> and doesn’t look easy to prove, although conceptually it’s not complicated. With
> univalence, closure under Pi doesn’t look difficult to prove either. On the
> other hand, it could be argued that it’s not necessary for the new theorems to
> be hard to make the work valuable.
> 
> There is also the question of whether this paper can be shrunk to 25 LNCS pages.
> I’m not sure about this, and will leave this question to the authors.
> 
> ## Reviewer's Confidence
> 
> 4: (high)
> 
> ## Questions for authors
> 
> 1. Could you clarify exactly which definitions and theorems are new?

Yes absolutely.

The fully new proofs in the paper are:

- Theorem 2.7, showing that any cardinal finite type with a total order is
  Bishop finite.
- Theorem 3.4, showing that any cardinal finite set forms a Π-Pretopos.
- Manifest enumerability is a new definition, as far as we are aware.

Of course, these theorems have some sub-lemmas that are also new (and others
that have been proven before); we will identify which is which inline in an
update.

> 2. Could you fix the countdown example or provide some more examples to
>    demonstrate the full power of your library (which I suppose is the ability to
>    deal with function types)?

Answered above: we will make the countdown example use function types.

> 3. Just curious: how (in)efficient is your solution to the countdown problem?

The example in the paper takes a few seconds to typecheck.

> 4. How would you plan to shrink this paper to 25 LNCS pages?

As suggested above, we will shorten the discussion of theorems already proven
elsewhere, and instead focus on a high-level summary of the classification of
predicates, and leave the in-depth proofs for the novel work

> ## Detailed comments for authors
> 
> * L88 (and throughout the paper) ‘dependently-typed’: The hyphen is not needed.
>   (You do write ‘dependently typed’ in some other places of the paper.)

Fixed

> * L124 ‘Section 2.4’, ‘Section 2.1’: put parentheses around these

Fixed

> * L166 fiber: ∃ usually means mere existence in HoTT, but I don’t suppose the
>   type here is truncated?

It is not truncated. This is the cubical Agda convention, which does differ from
the HoTT convention.

> * L177: Does ‘equivalent’ here mean equivalence in HoTT (defined in the paper at
>   L303)?

The precise property proven here is actually isomorphism, but of course this is
equivalent to equivalence by univalence.

> * L179: Some parts of the formula/code are italicised by the lemma environment
>   but these look weird.

Fixed

> * L393 ‘More importantly [Hedberg’s theorem]... And of course we know that A
>   here has decidable equality.’: This proof seems circular. We’re proving
>   Discrete A, that is, A has decidable equality, and one thing we need to
>   establish is that Discrete A is a proposition, which is reduced to the
>   condition that A is a set, at which point we don’t know A has decidable
>   equality yet and cannot use Hedberg’s theorem? 

The condition that `Discrete A` is a proposition is given as:

      isProp (Discrete A)
    = ∀ (x y : Discrete A) → x ≡ y

Meaning that, when trying to prove that the type `Discrete A` is a proposition,
we have available to us two proofs that `A` is discrete, so we can indeed rely 
on `A` being a set in this context.

>   The statement of Lemma 2.5
>   seems to suppose A is a set however, so this last part of the proof isn’t
>   actually needed.

There seems to be some confusion here.
Lemma 2.5 proves that A is a set, it does not take that as an assumption.

> * L413 ‘‖map‖’, ‘B⇒Fin≃’: should at least give the types (for all the
>   definitions throughout the paper; I think there are others that are left
>   undefined too)

We will add the signatures.

> * L416 ‘fin’ -> Fin (Agda code)

Fixed.

> * L445 ‘total order’: Should this total order be decidable?

Yes. We will make this clear.

> * L445 ‘Bishop finite’ -> manifestly Bishop finite

Will fix.

> * L481 & L484: C should be formatted consistently (throughout the paper)

Will fix.

> * L511 ‘every finiteness predicate we’ve seen implies decidable equality’: if
>   Lemma 2.5 pre-supposes A to be a set, then this argument needs fixing (because
>   Lemma 2.5 is not applicable to the circle, which is not a set).

Lemma 2.5 doesn't presuppose that A is a set.

> * L559: Some motivation for yet another form of finiteness is needed here.

Kuratowski finiteness is a standard notion of finiteness in constructive
mathematics, arguably more fundamental than the other predicates presented.
We will give more explanation as to the motivation in an update.

> * L607: Some motivation is needed here. In fact I don’t see why it’s important
>   to emphasise that finite sets form a category or a kind of topos. Wouldn’t it
>   suffice to say that we want closure under various dependent type formers?

Forming a Pi-pretopos is a stronger result than just proving that finite sets
have closure under the various toposes.
The Pi-pretopos is a relatively standard generalised setting for constructive
mathematics, see, for instance, Rijke and Spitters [2014], or
https://arxiv.org/abs/1207.0959 for a more in-depth exploration of it.
(although those study the Pi-W-pretopos)

> * L769–770: insert a comma after ‘Put another way’ and ‘Secondly’

Done

> * L1025 ‘That’s what we will figure out in this subsection’: This seems to refer
>   to a smaller subsection which probably has been edited away.

Fixed

> * L1028 ‘This doesn’t get us much closer to a finiteness proof, however: for
>   that we will need to rely on Dyck words’: I was expecting to generate binary
>   trees having a specified list of leaves (and there are finitely many such
>   trees). Would this be significantly harder?

Our approach decomposes the finiteness of the elements and the finiteness of the
tree shapes.
To do both at once would require the specification of a binary tree type with a
predicate that its leaves are equal (after flattening) to some list, which we
think is less clean.

> * The Agda code should have been submitted as supplementary material.

It will be submitted as an artefact.

--------------------------------------------------------------------------------
> # Review 4
> 
> ## Overall evaluation
> 
> 0: (weak accept / borderline (the paper can be accepted))
> The paper describes a Cubical Agda formalization of several results about finite
> sets, a proof search library based on that, and describes a verified proof
> search solution for Hutton's countdown problem.
> 
> First, I note some issues in the current submission.
> 
> - Most of the contribution in the paper is the Cubical Agda formalization, but I
>   don't see any supplementary material being uploaded. Is this an accidental
>   omission, or perhaps an EasyChair issue? In any case, being able to look at
>   the formalisation seems rather important here.

We were unsure when to submit the formalisation.
The plan is to submit it as an artefact, but we will see if it is possible to
submit during the review process.

> - A substantial part of the paper reviews definitions and theorems from previous
>   literature. There are relatively few new results about finite sets. I'd prefer
>   for the paper to focus on the novelties in the first half of the paper, and
>   then perhaps spend more space on the proof search library & its applications.

To get the paper to fit in the page limit we will shorten up the early parts
which focus on preexisting theorems.

>   However, even then I'd find the amount of novelty to be a bit low for a
>   research paper submission. It's also a bit hard to assess how substantial the
>   new formalizations are, without having access to the Agda code.
> - This last point is more like a nitpick: the usage of computational univalence
>   is mentioned in the paper but it could have been explored a bit more. As far
>   as I see, all novelties in the paper would have been straightforward to
>   formalize in plain (non-cubical) HoTT, with the exception of the proof search
>   library, but there it'd be nice too see more about how computational
>   univalence is being used.

It may well be possible to prove the main theorems in the paper without
computational univalence (although difficult: we use computation in a handful of
the internal proofs, but this is probably not essential).

> On the positive side, I found the paper highly readable, and I found the proof
> search solution for the countdown problem quite fun.
> 
> Overall I can't make a clear recommendation for publication for the current
> state of the submission.
> 
> ## Reviewer's Confidence
> 
> 3: (medium)
> 
> ## Questions for authors
> 
> none
> 
> ## Detailed comments for authors
> 
> Spelling, grammar, phrasing
> 
> 5: the present tense is a lot more commonly used in abstracts than the future
> tense, it'd look nicer to switch to that. The future tense sounds like as if
> the work hasn't been done yet. Also, line 35 for instance: "all our work will
> be formalised in Agda" very much sounds like it hasn't yet been formalised!

Fixed.
> 
> 26: "in particular Cubical Agda" should be moved out of the citation bracket

Fixed.

> 
> 31: "quantities like a total order" --> maybe "data like a total ordering"

Fixed.

> 72: The two citations to Frumin et al. that are next to each other could be
> replaced with one citation.

This is fixed by changing to the llncs style.

> 100: "Non Discrete" --> "Non-discrete"

Fixed.

> 114, Fig. 1: usually, terminology is not capitalized in mathematical English,
> so I'd prefer to not capitalize "Split Enumerable", "Cardinal finite", etc.
> Also in the text.

Will fix.

> 124: Parentheses seem to be missing around "Section 2.4" and "Section 2.1"

Fixed.

> General comment on formatting: I prefer if the inserted code examples are
> indented to some degree. Now the Agda snippets start in the first column
> everywhere.

Will fix.

> 328: the footnote superscript should go after the punctuation

Fixed

> 370: "out from under the truncation" --> "from under the truncation" is enough

Fixed

> 511: "Hedberg's theorem says every" --> "Hedberg's theorem says that every"

Fixed

> 570: "equations that usage of the type must obey" sounds awkward

Rephrased to:

The next two constructors add extra equations (paths) to the type.
For a function to be well-defined on K A it must respect these
equations (and the type checker enforces this condition).
 
> 576: "in its own right" --> "on its own right"
> 
> 578: "of that type" --> "of the type"

Fixed
> 
> 737: "dependently-typed" --> "dependently typed"

Fixed

> "proofs of interesting theoretical things" --> maybe use a bit more refined
> wording
> 
> 832: "decidable types can eliminate from double negation" -->
> "double negation can be eliminated for decidable types"
> 
> 902: place footnote superscript after the full stop
> 
> 918: "step one." --> "step one"
> 
> 1171: "dependently-typed, proof perspective" --> "proof perspective" doesn't
> read right; maybe "ours is the first paper to provide a dependently typed and
> verified solution to the countdown problem"
> 
> 1189: "in dependently typed language" --> "in a dependently typed language"
> 
> 
> Other comments:
> 
> 38: It might be good to cite https://dl.acm.org/doi/10.1145/3209108.3209197 for
> the underlying theory, since that version is the closest to Cubical Agda.
> 
> 250: I've never seen "contraction" being used to mean "contractible type".
> In the HoTT book, "contraction" by itself refers to the function that
> connects values to the "center of contraction".
> So you should use "contractible type" as well.

Fixed

> 
> Section 2.3
> perhaps the discussion of h-propositions and prop-truncations could
> be omitted, and you could refer to e.g. the HoTT book.

Will fix

 
> 440:
> maybe give a reference to a prior proof of Fin's injectivity?

Will fix
