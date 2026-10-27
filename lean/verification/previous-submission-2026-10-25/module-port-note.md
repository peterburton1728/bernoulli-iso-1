# Generated simp helper module-port diagnosis

The root-owned build reported unknown private
`_private.UpstreamConstruction.0.Equiv.Perm.SameCycle.rfl._simp_1` in the
exposed data definitions `WeakBalanced.mergeWhite` and `mergeBlack`.
Source inspection identifies the cause: `[local simp] SameCycle.rfl` creates a
preprocessed private simp auxiliary (first registration in the bundle near line
2507). The simp preprocessor uses `mkAuxLemma` with kind `_simp`, while local
attribute registration disables exporting. Later public exposed definitions use
this helper in their proof fields.

Minimal formatting-only compatibility fix, to be made by root:

```lean
module
public import UpstreamFoundation
set_option backward.privateInPublic true
@[expose] public section
```

It must occur before the helper is generated, rather than merely around the
later definitions. Keep warnings enabled. Bundled `Lean/ResolveName.lean:105`
explicitly defines this migration option to export private declarations while
porting to modules. `Lean/AddDecl.lean:138–141` implements that export. This
changes visibility of generated auxiliaries, no hypothesis, theorem statement,
formula, or proof body.

If root chooses the narrower proof-only workaround instead, the black hn step
can be replaced by `intro h; exact ha h.of_apply_right`. The white step can
similarly introduce h, change its target to
`R.white.SameCycle a (R.white (R.black a))`, and apply `ha h.of_apply_right`.
This avoids simp's helper, but changes a proof body and is less suitable when
the goal is a purely formatting/module port.

No Lean/compiler execution or release modification by this reviewer. Root owns
the validating build; success is not asserted. Tactical success factor 9/10;
superego: diagnosis and supported migration option only, no mathematical repair.
