Algebraic categories
====================

This repository contains a preliminary experiment to model algebraic
categories using MathComp and HierarchyBuilder. The main goal was to properly
get the adjunction of the free algebra (resp. free commutative algebra)
functor with the forgetful functor to set. The file `category.v` is largely
copied and adapted to an axiom free context from
https://github.com/affeldt-aist/monae various thing in this development need
to be backported. I'm very grateful to the monae developers for their work.

Here are some difficulties encountered during the development process:

- Support for some setoid rewrite in particular for `=1` and `\o` would be
  super useful. For example, the following computation is currently very
  tedious: suppose that you now that `f =1 idfun` where `f` is a morphism
  `{hom a -> b}` in some category. Recall that `F # f` is the application of
  the functor `F` to `f`. Then this should be three rewrites
  `F # f \o h =1 F # idfun \o h =1 idfun \o h =1 h`.
  Currently lot's of time is spend in precisely folding and unfolding map
  compositions. See for example
  https://github.com/hivert/Adjoint/blob/55353be6bbf1e8e086ee9cf977844a9cb67fb40d/theories/algcat.v#L1762-L1771
- Lots of the code in
  https://github.com/hivert/Adjoint/blob/main/theories/algcat.v
  could be automatically generated in particular the declaration of a category
  and the definition of forgetful functors.

- I didn't properly set up the morphisms. For example, a `LModules`-morphism
  is *not* a linear function but can only be coerced from and to. As a
  consequence, defining a forgetful functor is not automatic. See in
  particular
  https://github.com/hivert/Adjoint/blob/55353be6bbf1e8e086ee9cf977844a9cb67fb40d/theories/algcat.v#L385-L386
  where a proof of `LModules_mor_semi_additive f` is needed.

- The fact that `monoidType` and `commonoidType` weren't in MathComp hierarchy
  made things considerably harder since it made the additive forget paths
  `SemiRings -> NModules -> Sets` and the multiplicative path
  `SemiRings -> Monoids -> Sets` en up in a different sets. This can be fixed
  using natural transformations but is a little bit accrobatic. See 
  https://github.com/hivert/Adjoint/blob/55353be6bbf1e8e086ee9cf977844a9cb67fb40d/theories/algcat.v#L1704-L1719
  and is usage in
  https://github.com/hivert/Adjoint/blob/55353be6bbf1e8e086ee9cf977844a9cb67fb40d/theories/algcat.v#L2123-L2130

  Another example with commutative monoids:
  https://github.com/hivert/Adjoint/blob/55353be6bbf1e8e086ee9cf977844a9cb67fb40d/theories/algcat.v#L2488-L2506
  I learned a lot about natural transformation doing that :-)

- I'm not good at putting the proper locking at the proper place. There are
  place in the proof where one strive to avoid calling `/=`. TODO : find some
  place. This might be partially fixed by using Records instead of lock in
  more recent versions.

- Also, when using
  large composition of natural transformation, Coq can take quite some time
  such as 20s for the QED of
  https://github.com/hivert/Adjoint/blob/55353be6bbf1e8e086ee9cf977844a9cb67fb40d/theories/algcat.v#L2545-L2552

I'll add more comment if I think of some.
