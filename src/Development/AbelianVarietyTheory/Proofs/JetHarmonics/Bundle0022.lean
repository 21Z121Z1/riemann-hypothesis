import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfProdLinear

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRepresentableOfCover
section
noncomputable section

namespace GlobalTheory.GenTorsor

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X Y Z : Scheme.{0}}

def pb (a : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (h : W ≤ a ⁻¹ᵁ U) : Γ(X, U)ˣ →* Γ(Y, W)ˣ :=
  Units.map (a.appLE U W h).hom

lemma pb_pb (b : Z ⟶ Y) (a : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (h : V ≤ a ⁻¹ᵁ U) (h' : W ≤ b ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    pb b V W h' (pb a U V h x) = pb (b ≫ a) U W (h'.trans (b.preimage_mono h)) x := by
  ext
  change ((a.appLE U V h ≫ b.appLE V W h').hom) (x : Γ(X, U)) = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

lemma pb_congr {a b : Y ⟶ X} (e : a = b) {U : X.Opens} {W : Y.Opens} (h : W ≤ a ⁻¹ᵁ U)
    (h' : W ≤ b ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pb a U W h x = pb b U W h' x := by
  subst e; rfl

lemma res_pullU (a : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (h : W ≤ a ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU a U x) = pb a U W h x := rfl

lemma res_eq_pb {U W : X.Opens} (h : W ≤ U) (x : Γ(X, U)ˣ) : res h x = pb (𝟙 X) U W h x := rfl

lemma pb_id {U : X.Opens} (h : U ≤ (𝟙 X) ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pb (𝟙 X) U U h x = x := by
  rw [← res_eq_pb (le_refl U)]
  ext
  change (X.presheaf.map (𝟙 _)).hom _ = _
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma res_pb (a : Y ⟶ X) {U : X.Opens} {V W : Y.Opens}
    (h : V ≤ a ⁻¹ᵁ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (pb a U V h x) = pb a U W (le_trans h' h) x :=
  (pb_pb (𝟙 Y) a h h' x).trans (pb_congr (Category.id_comp a) _ _ _)

lemma pb_res (a : Y ⟶ X) {U V : X.Opens} {W : Y.Opens}
    (h : V ≤ U) (h' : W ≤ a ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    pb a V W h' (res h x) = pb a U W (h'.trans (a.preimage_mono h)) x :=
  (pb_pb a (𝟙 X) h h' x).trans (pb_congr (Category.comp_id a) _ _ _)

lemma res_self {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)ˣ) : res h x = x := pb_id h x

lemma pb_bijective (a : Y ⟶ X) [IsOpenImmersion a] {U : X.Opens} (hU : U ≤ a.opensRange)
    {W : Y.Opens} (h : W = a ⁻¹ᵁ U) : Function.Bijective (pb a U W h.le) := by
  subst h
  have := a.isIso_app U hU
  have e : a.appLE U (a ⁻¹ᵁ U) le_rfl = a.app U := (a.app_eq_appLE).symm
  have h2 : pb a U (a ⁻¹ᵁ U) le_rfl =
      (Units.mapEquiv (asIso (a.app U)).commRingCatIsoToRingEquiv.toMulEquiv).toMonoidHom := by
    ext x
    change (a.appLE U (a ⁻¹ᵁ U) le_rfl).hom _ = _
    rw [e]; rfl
  rw [h2]
  exact (Units.mapEquiv _).bijective

lemma unit_ext_opens {J : Type*} {V : X.Opens} (W : J → X.Opens) (hW : ∀ i, W i ≤ V)
    (hc : V ≤ iSup W) {u v : Γ(X, V)ˣ}
    (h : ∀ i, res (hW i) u = res (hW i) v) : u = v := by
  ext
  exact X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc _ _
    fun i => congrArg Units.val (h i)

lemma unit_glue_opens {J : Type*} (V : X.Opens) (W : J → X.Opens) (hW : ∀ i, W i ≤ V)
    (hc : V ≤ iSup W) (u : ∀ i, Γ(X, W i)ˣ)
    (hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res inf_le_right (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, res (hW i) s = u i := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => (u i).val) (fun i j => congrArg Units.val (hh i j))
  obtain ⟨s', hs', -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => ((u i)⁻¹).val)
    (fun i j => congrArg Units.val
      (show res (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹ = res inf_le_right (u j)⁻¹ by
        rw [map_inv, map_inv, hh]))
  have e : (show Γ(X, V) from s) * (show Γ(X, V) from s') = 1 := by
    apply X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
    intro i
    show (X.presheaf.map (homOfLE (hW i)).op).hom _ = (X.presheaf.map (homOfLE (hW i)).op).hom _
    rw [map_mul, map_one]
    exact (congrArg₂ (· * ·) (hs i) (hs' i)).trans (u i).mul_inv
  exact ⟨⟨s, s', e, (mul_comm _ _).trans e⟩, fun i => Units.ext (hs i)⟩

section Cover

variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

lemma le_iSup_range (hc : ∀ x : X, ∃ i y, a i y = x) (V : X.Opens) :
    V ≤ ⨆ i, V ⊓ (a i).opensRange := fun x hx => by
  obtain ⟨i, y, rfl⟩ := hc x
  exact Opens.mem_iSup.2 ⟨i, hx, y, rfl⟩

lemma preimage_inf_range (i : J) (V : X.Opens) :
    a i ⁻¹ᵁ V = a i ⁻¹ᵁ (V ⊓ (a i).opensRange) := by
  ext y
  exact ⟨fun h => ⟨h, y, rfl⟩, fun h => h.1⟩

lemma unit_ext_cover (hc : ∀ x : X, ∃ i y, a i y = x) {V : X.Opens} {u v : Γ(X, V)ˣ}
    (h : ∀ i, pb (a i) V _ le_rfl u = pb (a i) V _ le_rfl v) : u = v := by
  refine unit_ext_opens _ (fun i => inf_le_left) (le_iSup_range a hc V) fun i => ?_
  apply (pb_bijective (a i) inf_le_right (preimage_inf_range a i V)).1
  rw [pb_res, pb_res]
  exact h i

lemma unit_glue_cover (hc : ∀ x : X, ∃ i y, a i y = x) (V : X.Opens)
    (u : ∀ i, Γ(T i, a i ⁻¹ᵁ V)ˣ)
    (h : ∀ i j (S : Scheme.{0}) (b : S ⟶ T i) (c : S ⟶ T j), b ≫ a i = c ≫ a j →
      ∀ (hb : ⊤ ≤ b ⁻¹ᵁ a i ⁻¹ᵁ V) (hc : ⊤ ≤ c ⁻¹ᵁ a j ⁻¹ᵁ V),
        pb b _ ⊤ hb (u i) = pb c _ ⊤ hc (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, pb (a i) V _ le_rfl s = u i := by
  choose w hw using fun i => (pb_bijective (a i) inf_le_right (preimage_inf_range a i V)).2 (u i)
  obtain ⟨s, hs⟩ := unit_glue_opens V _ (fun i => inf_le_left) (le_iSup_range a hc V) w (by
    intro i j
    set W := V ⊓ (a i).opensRange ⊓ (V ⊓ (a j).opensRange) with hW
    have hi : Set.range W.ι ⊆ Set.range (a i) := by
      rw [Scheme.Opens.range_ι]; exact fun x hx => hx.1.2
    have hj : Set.range W.ι ⊆ Set.range (a j) := by
      rw [Scheme.Opens.range_ι]; exact fun x hx => hx.2.2
    have ei := IsOpenImmersion.lift_fac (a i) W.ι hi
    have ej := IsOpenImmersion.lift_fac (a j) W.ι hj
    have hT : (⊤ : W.toScheme.Opens) = W.ι ⁻¹ᵁ W := by simp
    have hV : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ V :=
      hT.le.trans (W.ι.preimage_mono (inf_le_left.trans inf_le_left))
    apply (pb_bijective W.ι (U := W) (by simp) hT).1
    have := h i j W _ _ (ei.trans ej.symm)
      (by rw [← Scheme.Hom.comp_preimage, ei]; exact hV)
      (by rw [← Scheme.Hom.comp_preimage, ej]; exact hV)
    rw [← hw, ← hw, pb_pb, pb_pb] at this
    rw [pb_res, pb_res]
    exact (pb_congr ei.symm _ _ _).trans (this.trans (pb_congr ej _ _ _)))
  refine ⟨s, fun i => ?_⟩
  rw [← hw, ← hs, pb_res]

end Cover

theorem exists_universal_units (K : Type) :
    ∃ (T : Scheme.{0}) (e : K → Γ(T, ⊤)ˣ), ∀ (Z : Scheme.{0}) (u : K → Γ(Z, ⊤)ˣ),
      ∃! c : Z ⟶ T, ∀ k, pb c ⊤ ⊤ le_rfl (e k) = u k := by
  let A := MonoidAlgebra ℤ (Multiplicative (FreeAbelianGroup K))
  let ε : K → Aˣ := fun k =>
    (MonoidAlgebra.of ℤ (Multiplicative (FreeAbelianGroup K))).toHomUnits
      (Multiplicative.ofAdd (FreeAbelianGroup.of k))
  have hext : ∀ (R : Type) [CommRing R] (φ ψ : A →+* R), (∀ k, φ (ε k) = ψ (ε k)) → φ = ψ := by
    intro R _ φ ψ h
    have : (φ.toMonoidHom.comp (MonoidAlgebra.of ℤ _)).toHomUnits =
        (ψ.toMonoidHom.comp (MonoidAlgebra.of ℤ _)).toHomUnits := by
      apply MonoidHom.toAdditiveRight.injective
      apply FreeAbelianGroup.lift.symm.injective
      funext k
      exact congrArg Additive.ofMul (Units.ext (h k))
    apply MonoidAlgebra.ringHom_ext
    · intro b; exact (eq_intCast (φ.comp MonoidAlgebra.singleOneRingHom) b).trans
        (eq_intCast (ψ.comp MonoidAlgebra.singleOneRingHom) b).symm
    · intro g
      exact congrArg (fun f => (f g : R)) this
  have hex : ∀ (R : Type) [CommRing R] (u : K → Rˣ), ∃ φ : A →+* R, ∀ k, φ (ε k) = u k := by
    intro R _ u
    refine ⟨(MonoidAlgebra.lift ℤ R _ ((Units.coeHom R).comp (MonoidHom.toAdditiveRight.symm
      (FreeAbelianGroup.lift fun k => Additive.ofMul (u k))))).toRingHom, fun k => ?_⟩
    simp [ε, A]
  let i := Scheme.ΓSpecIso (CommRingCat.of A)
  refine ⟨Spec (.of A), fun k => Units.map i.inv.hom (ε k), fun Z u => ?_⟩
  have hpb : ∀ (c : Z ⟶ Spec (.of A)) k,
      (pb c ⊤ ⊤ le_rfl (Units.map i.inv.hom (ε k))).val = (i.inv ≫ c.appTop).hom (ε k) := by
    intro c k
    have e : c.appLE ⊤ ⊤ le_rfl = c.appTop := (c.app_eq_appLE (U := ⊤)).symm
    change (c.appLE ⊤ ⊤ le_rfl).hom _ = _
    rw [e]; rfl
  obtain ⟨φ, hφ⟩ := hex _ u
  refine existsUnique_of_exists_of_unique ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), fun k => ?_⟩ ?_
  · apply Units.ext
    rw [hpb, ← hφ]
    have : i.inv ≫ (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop = CommRingCat.ofHom φ := by
      simp [i, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    rw [this]; rfl
  · intro c c' h h'
    apply ext_of_isAffine
    rw [← cancel_epi i.inv]
    ext1
    apply hext
    intro k
    rw [← hpb, ← hpb, h, h']

theorem isRepresentable_of_cover (F : Scheme.{0}ᵒᵖ ⥤ Type)
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) (p : F ⟶ yoneda.obj X)
    {J : Type} (W : J → X.Opens) (hW : iSup W = ⊤) (T : J → Scheme.{0})
    (y : ∀ i, F.obj (op (T i))) (π : ∀ i, T i ⟶ W i)
    (hπ : ∀ i, p.app _ (y i) = π i ≫ (W i).ι)
    (h : ∀ i (Z : Scheme.{0}) (x : F.obj (op Z)) (b : Z ⟶ W i), p.app _ x = b ≫ (W i).ι →
      ∃! c : Z ⟶ T i, F.map c.op (y i) = x) : F.IsRepresentable := by
  let G : Sheaf Scheme.zariskiTopology.{0} Type := ⟨F, (isSheaf_iff_isSheaf_of_type _ _).2 hF⟩
  let f : ∀ i, yoneda.obj (T i) ⟶ G.1 := fun i => yonedaEquiv.symm (y i)
  have hp : ∀ i (Z : Scheme.{0}) (c : Z ⟶ T i), p.app _ (F.map c.op (y i)) = c ≫ π i ≫ (W i).ι := by
    intro i Z c
    rw [← hπ]
    exact ConcreteCategory.congr_hom (p.naturality c.op) (y i)
  have hf : ∀ i, IsOpenImmersion.presheaf (f i) := by
    intro i
    have : IsPullback (f i) (yoneda.map (π i)) p (yoneda.map (W i).ι) := by
      apply IsPullback.of_forall_isPullback_app
      rintro ⟨Z⟩
      rw [Types.isPullback_iff]
      refine ⟨?_, ?_, ?_⟩
      · ext c
        exact (hp i Z c).trans (Category.assoc _ _ _).symm
      · rintro c c' ⟨h1, -⟩
        exact (h i Z (F.map (Quiver.Hom.op c) (y i)) (c ≫ π i)
          ((hp i Z c).trans (Category.assoc _ _ _).symm)).unique rfl h1.symm
      · intro x b hb
        obtain ⟨c, hc, -⟩ := h i Z x b hb
        refine ⟨c, hc, ?_⟩
        change c ≫ π i = b
        rw [← cancel_mono (W i).ι, Category.assoc, ← hp, hc]
        exact hb
    exact (MorphismProperty.relative_isStableUnderBaseChange @IsOpenImmersion).of_isPullback this.flip
      (MorphismProperty.relative_map (inferInstanceAs (IsOpenImmersion (W i).ι)))
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
    constructor
    intro Z x
    let q : Z ⟶ X := p.app _ x
    let 𝒰 := Z.openCoverOfIsOpenCover (fun i => q ⁻¹ᵁ W i) (by
      rw [IsOpenCover, ← Scheme.Hom.preimage_iSup, hW]; rfl)
    refine GrothendieckTopology.superset_covering _ ?_ 𝒰.mem_grothendieckTopology
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    obtain ⟨c, hc, -⟩ := h i _ (F.map (q ⁻¹ᵁ W i).ι.op x) (q ∣_ W i) (by
      rw [morphismRestrict_ι]
      exact ConcreteCategory.congr_hom (p.naturality (q ⁻¹ᵁ W i).ι.op) x)
    refine ⟨(Sigma.ι (fun i => yoneda.obj (T i)) i).app _ c, ?_⟩
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (Sigma.ι_desc f i) _) c).trans hc
  exact Scheme.LocalRepresentability.isRepresentable hf

end GlobalTheory.GenTorsor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RingHomPointBijective
section
open PowerSeries GlobalTheory.MomOne WeierstrassCurve WeierstrassCurve.Affine
open scoped ComplexConjugate BigOperators Topology
open Classical

noncomputable section

namespace GlobalTheory.MomOne

def ringHomPointFun {k k' : Type*} [Field k] [Field k'] (f : k →+* k') (W : WeierstrassCurve k) :
    W.toAffine.Point → (W.map f).toAffine.Point
  | .zero => 0
  | .some x y hP => .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr hP)

def ringHomPoint {k k' : Type*} [Field k] [Field k'] (f : k →+* k') (W : WeierstrassCurve k) :
    W.toAffine.Point →+ (W.map f).toAffine.Point :=
  AddMonoidHom.mk' (ringHomPointFun f W) <| by
    refine GlobalTheory.map_add_of_triples _ rfl ?_ ?_
    · rintro (_ | ⟨x, y, hP⟩)
      · rfl
      · simp only [Point.neg_some, ringHomPointFun, Point.some.injEq, true_and, negY,
          map_a₁, map_a₃, map_sub, map_neg, map_mul]
    · rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) (_ | ⟨x₃, y₃, h₃⟩) hP hQ hR h
      any_goals first | exact absurd rfl hP | exact absurd rfl hQ | exact absurd rfl hR
      obtain ⟨l, n, e₁, e₂, e₃, s₁, s₂, -⟩ := GlobalTheory.exists_line_of_add_add_eq_zero h
      refine GlobalTheory.add_add_eq_zero_of_line _ _ _ (f l) (f n) ?_ ?_ ?_ ?_ ?_
      · rw [e₁]; simp
      · rw [e₂]; simp
      · rw [e₃]; simp
      · simpa using congrArg f s₁
      · simpa [map_ofNat] using congrArg f s₂

open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
private lemma ringHomPoint_some {k k' : Type*} [Field k] [Field k']
    (f : k →+* k') (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    _root_.GlobalTheory.MomOne.ringHomPoint f W (.some x y h) =
      .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr h) := rfl

open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
private lemma ringHomPoint_surjective_of_ringEquiv {k k' : Type*} [Field k] [Field k']
    (e : k ≃+* k') (W : WeierstrassCurve k) :
    Function.Surjective (_root_.GlobalTheory.MomOne.ringHomPoint (e : k →+* k') W) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, map_zero _⟩
  · have h' : W.toAffine.Nonsingular (e.symm x) (e.symm y) := by
      rw [← WeierstrassCurve.Affine.map_nonsingular W.toAffine (f := (e : k →+* k')) e.injective]
      simpa using h
    refine ⟨.some _ _ h', ?_⟩
    rw [ringHomPoint_some]
    simp

open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
private lemma ringHomPoint_eq_zero_iff {k k' : Type*} [Field k] [Field k']
    (f : k →+* k') (W : WeierstrassCurve k) (P : W.toAffine.Point) :
    _root_.GlobalTheory.MomOne.ringHomPoint f W P = 0 ↔ P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [ringHomPoint_some]
    simp

open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in

theorem _root_.GlobalTheory.MomOne.Mdl.exists_pointHom (q : ℕ) [Fact q.Prime]
    (M : _root_.GlobalTheory.MomOne.Mdl q) (hM : M.Ok) :
    ∃ φ : ℂ →+ M.W.toAffine.Point, Function.Surjective φ ∧
      (∀ z, φ z = 0 ↔ z ∈ M.L.lattice) ∧
      ∀ z ∉ M.L.lattice, ∃ h,
        φ z = WeierstrassCurve.Affine.Point.some (M.ι (M.x z))
          (M.ι (M.y z)) h := by
  obtain ⟨hc, -, -, -, -, -, -, h₄, h₆⟩ := hM
  have hιc : M.ι M.c ≠ 0 :=
    (map_ne_zero M.ι).mpr hc
  obtain ⟨C, hCu, hCr, hCs, hCt⟩ : ∃ C : VariableChange ℂ_[q],
      (C.u : ℂ_[q]) = (M.ι M.c)⁻¹ ∧
      C.r = -(M.W.b₂ / 12) ∧ C.s = -(M.W.a₁ / 2) ∧
      C.t = M.W.a₁ * M.W.b₂ / 24 -
        M.W.a₃ / 2 :=
    ⟨⟨Units.mk0 _ (inv_ne_zero hιc), _, _, _⟩, rfl, rfl, rfl, rfl⟩
  have hCu' : ((C.u⁻¹ : ℂ_[q]ˣ) : ℂ_[q]) = M.ι M.c := by
    rw [Units.val_inv_eq_inv_val, hCu, inv_inv]
  have hE : (_root_.GlobalTheory.latticeCurve M.L).a₁ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₂ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₃ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₄ = -M.L.g₂ / 4 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₆ = -M.L.g₃ / 4 := by
    simp [_root_.GlobalTheory.latticeCurve]
  obtain ⟨hE₁, hE₂, hE₃, hE₄, hE₆⟩ := hE
  have hg₂ : M.ι M.L.g₂ =
      M.W.c₄ / 12 * M.ι M.c ^ 4 := by
    rw [h₄, map_div₀, map_pow, div_mul_cancel₀ _ (pow_ne_zero 4 hιc)]
  have hg₃ : M.ι M.L.g₃ =
      M.W.c₆ / 216 * M.ι M.c ^ 6 := by
    rw [h₆, map_div₀, map_pow, div_mul_cancel₀ _ (pow_ne_zero 6 hιc)]
  have hC : C • M.W =
      (_root_.GlobalTheory.latticeCurve M.L).map (M.ι : ℂ →+* ℂ_[q]) := by
    ext
    · rw [variableChange_a₁, hCu', hCs, map_a₁, hE₁]; simp only [map_zero]; ring
    · rw [variableChange_a₂, hCu', hCs, hCr, map_a₂, hE₂]
      simp only [map_zero, WeierstrassCurve.b₂]; ring
    · rw [variableChange_a₃, hCu', hCt, hCr, map_a₃, hE₃]
      simp only [map_zero, WeierstrassCurve.b₂]; ring
    · rw [variableChange_a₄, hCu', hCs, hCt, hCr, map_a₄, hE₄]
      simp only [RingHom.coe_coe, map_div₀, map_neg, map_ofNat, hg₂, WeierstrassCurve.c₄,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      ring
    · rw [variableChange_a₆, hCu', hCt, hCr, map_a₆, hE₆]
      simp only [RingHom.coe_coe, map_div₀, map_neg, map_ofNat, hg₃, WeierstrassCurve.c₆,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      ring
  let φ : ℂ →+ M.W.toAffine.Point :=
    (_root_.GlobalTheory.variableChangePoint C hC).comp
      ((_root_.GlobalTheory.MomOne.ringHomPoint (M.ι : ℂ →+* ℂ_[q])
        (_root_.GlobalTheory.latticeCurve M.L)).comp
        (_root_.GlobalTheory.latticePointHom M.L))
  have hφ : ∀ z, φ z = _root_.GlobalTheory.variableChangePoint C hC
      (_root_.GlobalTheory.MomOne.ringHomPoint (M.ι : ℂ →+* ℂ_[q])
        (_root_.GlobalTheory.latticeCurve M.L)
        (_root_.GlobalTheory.latticePoint M.L z)) := by
    intro z
    simp only [φ, AddMonoidHom.coe_comp, Function.comp_apply, _root_.GlobalTheory.latticePointHom_apply]
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro P
    obtain ⟨P₁, rfl⟩ := (_root_.GlobalTheory.variableChangePoint_bijective C hC).2 P
    obtain ⟨P₂, rfl⟩ := ringHomPoint_surjective_of_ringEquiv M.ι _ P₁
    obtain ⟨z, rfl⟩ := _root_.GlobalTheory.latticePoint_surjective M.L P₂
    exact ⟨z, hφ z⟩
  · intro z
    rw [hφ, map_eq_zero_iff _ (_root_.GlobalTheory.variableChangePoint_bijective C hC).1,
      ringHomPoint_eq_zero_iff, _root_.GlobalTheory.latticePoint_eq_zero_iff]
  · intro z hz
    have key : ∀ {a b a' b' : ℂ_[q]} (h : M.W.toAffine.Nonsingular a b),
        a = a' → b = b' → ∃ h', (Point.some a b h : M.W.toAffine.Point) =
          Point.some a' b' h' := by
      rintro a b a' b' h rfl rfl
      exact ⟨h, rfl⟩
    have hx : (C.u : ℂ_[q]) ^ 2 * M.ι (M.L.weierstrassP z) + C.r =
        M.ι (M.x z) := by
      show _ = M.ι (M.L.weierstrassP z / M.c ^ 2 -
        M.ι.symm (M.W.b₂ / 12))
      rw [map_sub, map_div₀, map_pow, RingEquiv.apply_symm_apply, hCu, hCr]
      field_simp
      ring
    have hy : (C.u : ℂ_[q]) ^ 3 * M.ι (M.L.derivWeierstrassP z / 2) +
        (C.u : ℂ_[q]) ^ 2 * C.s * M.ι (M.L.weierstrassP z) + C.t =
        M.ι (M.y z) := by
      show _ = M.ι ((M.L.derivWeierstrassP z /
        M.c ^ 3 - M.ι.symm M.W.a₁ *
        M.x z - M.ι.symm M.W.a₃) / 2)
      simp only [map_div₀, map_sub, map_mul, map_pow, RingEquiv.apply_symm_apply, map_ofNat]
      rw [← hx, hCu, hCr, hCs, hCt]
      field_simp
      ring
    rw [hφ, _root_.GlobalTheory.latticePoint_of_notMem M.L hz,
      ringHomPoint_some, _root_.GlobalTheory.variableChangePoint_some]
    exact key _ hx hy

end GlobalTheory.MomOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdConstantCoeffDmonOfCols
section
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.SymbolCols

theorem colM_apply {ι : Type} [Finite ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) (b : Fin n) (l : ι) :
    colM m b l = m (l, b) := by
  simp [colM]

theorem sum_degree_colM {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) :
    ∑ b, (colM m b).degree = m.degree := by
  simp only [Finsupp.degree_eq_sum, colM_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem coeff_mul_congr {k σ : Type} [CommRing k] (N : ℕ) (f g E : MvPowerSeries σ k)
    (h : ∀ mo : σ →₀ ℕ, mo.degree ≤ N → coeff mo f = coeff mo g)
    (mo : σ →₀ ℕ) (hmo : mo.degree ≤ N) : coeff mo (f * E) = coeff mo (g * E) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = mo := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = mo.degree := by rw [← hp', map_add]
  rw [h p.1 (by omega)]

theorem exists_col {ι : Type} [Fintype ι] {n : ℕ} (m a : ι × Fin n →₀ ℕ)
    (hdeg : m.degree = a.degree) (hne : m ≠ a) :
    ∃ b, (colM m b).degree ≤ (colM a b).degree ∧ colM m b ≠ colM a b := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ b, (colM a b).degree ≤ (colM m b).degree := fun b => by
    by_contra h
    have := hcon b (by omega)
    rw [this] at h
    exact h le_rfl
  have hs : ∑ b, (colM a b).degree = ∑ b, (colM m b).degree := by
    rw [sum_degree_colM, sum_degree_colM, hdeg]
  have heq := (Finset.sum_eq_sum_iff_of_le fun b _ => hle b).1 hs
  refine hne (Finsupp.ext fun ⟨l, b⟩ => ?_)
  rw [← colM_apply, ← colM_apply, hcon b (heq b (Finset.mem_univ b)).ge]

end GlobalTheory.SymbolCols

namespace GlobalTheory

open SymbolCols in

theorem sum_prod_constantCoeff_dmonOf_cols :
    ∀ (R k : Type) [CommRing R] [CommRing k] (φ : R →+* k) (d : ℕ) (G : FGLaw R d) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (u : ι → Fin d → k) (lam : Fin n → ι → Fin d → k) (α : ι → k) (al : ι × Fin n →₀ ℕ) (P : MvPolynomial (ι × Fin n) k) (g E : Fin n → PS k 1 d), P.IsHomogeneous al.degree → (∀ b l l', al (l, b) ≠ 0 → (∃ mo ∈ P.support, mo (l', b) ≠ 0) → ∑ i, lam b l i * u l' i = if l = l' then α l else 0) → (∀ b (mo : Fin 1 × Fin d →₀ ℕ), mo.degree ≤ al.degree → coeff mo (g b) = coeff mo (∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b))) → ∑ mo ∈ P.support, P.coeff mo * ∏ b, constantCoeff (DmonOf (G.mapF φ) u (colM mo b) (g b * E b)) = P.coeff al * ∏ b, ((∏ l, ((al (l, b)).factorial : k) * α l ^ al (l, b)) * constantCoeff (E b)) := by
  intro R k _ _ φ d G ι _ _ n u lam α al P g E hP hpair hg
  have hdeg : ∀ mo ∈ P.support, mo.degree = al.degree := fun mo hmo => by
    have := hP (MvPolynomial.mem_support_iff.1 hmo)
    rw [← this, Finsupp.degree_eq_weight_one]
    rfl
  have hval : ∀ mo ∈ P.support, ∀ b, (colM mo b).degree ≤ (colM al b).degree →
      constantCoeff (DmonOf (G.mapF φ) u (colM mo b) (g b * E b)) =
        if colM mo b = colM al b then
          (∏ l, ((al (l, b)).factorial : k) * α l ^ al (l, b)) * constantCoeff (E b) else 0 := by
    intro mo hmo b hb
    have hle : (colM mo b).degree ≤ al.degree := by
      rw [← hdeg mo hmo, ← sum_degree_colM]
      exact Finset.single_le_sum (f := fun b => (colM mo b).degree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    rw [constantCoeff_DmonOf_congr_jet k d (G.mapF φ) ι u (colM mo b) _ _
      (fun m hm => coeff_mul_congr al.degree _ _ (E b) (hg b) m (hm.trans hle))]
    have := constantCoeff_dmonOf_prod_linear R k φ d G ι u (lam b) α (colM al b) (colM mo b) (E b)
      (fun l l' hl hl' => hpair b l l' (by rwa [colM_apply] at hl)
        ⟨mo, hmo, by rwa [colM_apply] at hl'⟩) hb
    simpa only [colM_apply] using this
  rw [Finset.sum_eq_single al]
  · by_cases hal : al ∈ P.support
    · congr 1
      exact Finset.prod_congr rfl fun b _ => by rw [hval al hal b le_rfl, if_pos rfl]
    · rw [MvPolynomial.notMem_support_iff.1 hal, zero_mul, zero_mul]
  · intro mo hmo hne
    obtain ⟨b, hb, hb'⟩ := exists_col mo al (hdeg mo hmo) hne
    rw [Finset.prod_eq_zero (Finset.mem_univ b) (by rw [hval mo hmo b hb, if_neg hb']), mul_zero]
  · intro hal
    rw [MvPolynomial.notMem_support_iff.1 hal, zero_mul]

end GlobalTheory
end

