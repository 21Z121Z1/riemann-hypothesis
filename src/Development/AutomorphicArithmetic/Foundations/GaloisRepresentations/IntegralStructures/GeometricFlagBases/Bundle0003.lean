import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagMove
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.flagMove_of :
    FlagMove := by
  intro Γ k _ _ d ρ W P W' hW' hJH
  have hPP : ∀ w : Fin d → k, (↑P : Matrix (Fin d) (Fin d) k).mulVec
      ((↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hPP' : ∀ w : Fin d → k, (↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec
      ((↑P : Matrix (Fin d) (Fin d) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hc : ∀ g v, (↑P : Matrix (Fin d) (Fin d) k).mulVec ((↑(cj P ρ g) : Matrix (Fin d) (Fin d) k).mulVec v) =
      (↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec ((↑P : Matrix (Fin d) (Fin d) k).mulVec v) := by
    intro g v
    rw [cj_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPP]
  refine ⟨fun i g v hv => ?_, fun i U hU h1 h2 => ?_⟩
  · rw [hW', hc]
    exact hJH.1 i g _ ((hW' i v).1 hv)
  · let U0 : Submodule k (Fin d → k) := U.map (Matrix.mulVecLin (↑P : Matrix (Fin d) (Fin d) k))
    have hmem : ∀ v, v ∈ U ↔ (↑P : Matrix (Fin d) (Fin d) k).mulVec v ∈ U0 := by
      intro v
      constructor
      · intro hv
        exact ⟨v, hv, rfl⟩
      · rintro ⟨u, hu, he⟩
        have huv : u = v := by
          have := congrArg (fun w => (↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w) he
          simpa [Matrix.mulVecLin_apply, hPP'] using this
        exact huv ▸ hu
    have hinv : IsInv ρ U0 := by
      rintro g w ⟨u, hu, rfl⟩
      refine ⟨(↑(cj P ρ g) : Matrix (Fin d) (Fin d) k).mulVec u, hU g u hu, ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact hc g u
    have hlo : W i ≤ U0 := by
      intro w hw
      refine ⟨(↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w, h1 ((hW' i _).2 (by rw [hPP]; exact hw)), ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact hPP w
    have hhi : U0 ≤ W (i + 1) := by
      rintro w ⟨u, hu, rfl⟩
      exact (hW' (i + 1) u).1 (h2 hu)
    rcases hJH.2 i U0 hinv hlo hhi with h | h
    · left
      ext v
      rw [hmem, h, hW']
    · right
      ext v
      rw [hmem, h, hW']
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PGrHom
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.grHom_of :
    GrHom := by
  intro Γ k _ _ d ρ₀ c hinv
  have mem : ∀ (i : ℕ) (v : Fin d → k), v ∈ low k c i ↔ ∀ j, i ≤ c j → v j = 0 :=
    fun _ _ => Iff.rfl
  have hbt : ∀ g, (ρ₀ g : Matrix (Fin d) (Fin d) k).BlockTriangular c := by
    intro g i j hij
    have hv : (Pi.single j (1 : k) : Fin d → k) ∈ low k c (c j + 1) := by
      rw [mem]
      intro j' hj'
      by_cases h : j' = j
      · subst h
        omega
      · simp [Pi.single_apply, h]
    have hw := (mem _ _).1 (hinv (c j + 1) g _ hv) i (by omega)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hw
  let D : Matrix (Fin d) (Fin d) k → Matrix (Fin d) (Fin d) k :=
    fun M => Matrix.of fun i j => if c i = c j then M i j else 0
  have hD : ∀ M i j, D M i j = if c i = c j then M i j else 0 := fun _ _ _ => rfl
  have hmul : ∀ M N : Matrix (Fin d) (Fin d) k, M.BlockTriangular c → N.BlockTriangular c →
      D (M * N) = D M * D N := by
    intro M N hM hN
    ext i j
    simp only [hD, Matrix.mul_apply]
    split_ifs with hij
    · apply Finset.sum_congr rfl
      intro l _
      by_cases h1 : c i = c l
      · rw [if_pos h1, if_pos (h1 ▸ hij)]
      · rw [if_neg h1, zero_mul]
        rcases lt_or_gt_of_ne h1 with h | h
        · rw [hN (show c j < c l by omega), mul_zero]
        · rw [hM h, zero_mul]
    · symm
      apply Finset.sum_eq_zero
      intro l _
      split_ifs with h1 h2 <;> simp_all
  have hone : D 1 = 1 := by
    ext i j
    simp only [hD, Matrix.one_apply]
    split_ifs <;> simp_all
  have hunit : ∀ g h : Γ, D (ρ₀ g) * D (ρ₀ h) = D (ρ₀ (g * h)) := by
    intro g h
    rw [← hmul _ _ (hbt g) (hbt h), map_mul, Units.val_mul]
  refine ⟨hbt, ⟨{ toFun := fun g => ⟨D (ρ₀ g), D (ρ₀ g⁻¹), ?_, ?_⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩⟩
  · rw [hunit, mul_inv_cancel, map_one, Units.val_one, hone]
  · rw [hunit, inv_mul_cancel, map_one, Units.val_one, hone]
  · apply Units.ext
    show D (ρ₀ 1) = 1
    rw [map_one, Units.val_one, hone]
  · intro x y
    apply Units.ext
    show D (ρ₀ (x * y)) = D (ρ₀ x) * D (ρ₀ y)
    rw [hunit]
  · intro g i j
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHopGal
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem comm_of_conj {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (A G G' : M →ₗ[R] M)
    (h : G ∘ₗ A ∘ₗ G' = A) (hid : G' ∘ₗ G = LinearMap.id) : A ∘ₗ G = G ∘ₗ A := by
  calc A ∘ₗ G = (G ∘ₗ A ∘ₗ G') ∘ₗ G := by rw [h]
    _ = G ∘ₗ A ∘ₗ (G' ∘ₗ G) := by simp only [LinearMap.comp_assoc]
    _ = G ∘ₗ A := by rw [hid, LinearMap.comp_id]

theorem UpperTheory.Gal.Int.Geo.hopGal_of :
    G3.HopSpec → OpConj → OpUniq → HopGal := by
  intro hS hC hU l _ k _ hl H Ω _ _ g d hd σ
  refine comm_of_conj _ _ (galTot l Ω H.q σ⁻¹)
    (hU l k hl H Ω g d hd _ (hC l k H Ω g _ σ (hS l hl H Ω g d hd).1)) ?_
  rw [← GlobalTheory.GalV.galTot_mul, inv_mul_cancel, GlobalTheory.GalV.galTot_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHtDesc
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo
open Opposite

noncomputable section

namespace UpperTheory.Gal.Int.Geo.HeightDescentDirectedColimits

section Alg
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]

private abbrev FI : Type := {L : IntermediateField k Ω // FiniteDimensional k L}

private theorem dir (a b : FI k Ω) : ∃ c : FI k Ω, a ≤ c ∧ b ≤ c := by
  have := a.2; have := b.2
  exact ⟨⟨a.1 ⊔ b.1, IntermediateField.finiteDimensional_sup _ _⟩, le_sup_left (a := a.1), le_sup_right (a := a.1)⟩

private instance : IsDirected (FI k Ω) (· ≤ ·) := ⟨dir k Ω⟩

private instance : Nonempty (FI k Ω) := ⟨⟨⊥, inferInstance⟩⟩

private instance : IsFiltered (FI k Ω) := isFiltered_of_directed_le_nonempty _

private def Dg : FI k Ω ⥤ CommRingCat.{0} where
  obj L := .of L.1
  map f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom
  map_id L := rfl
  map_comp f g := rfl

private def cg : Cocone (Dg k Ω) where
  pt := .of Ω
  ι := { app := fun L => CommRingCat.ofHom (algebraMap L.1 Ω)
         naturality := fun L L' f => rfl }

private theorem exists_rep [Algebra.IsAlgebraic k Ω] (x : Ω) : ∃ (L : FI k Ω) (y : L.1), algebraMap L.1 Ω y = x :=
  ⟨⟨IntermediateField.adjoin k {x}, IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral x)⟩, ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩, rfl⟩

private def cgColim [Algebra.IsAlgebraic k Ω] : IsColimit (cg k Ω) := by
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  refine isColimitOfReflects (forget _) (Types.FilteredColimit.isColimitOf _ _ (fun x => ?_) (fun i j xi xj h => ?_))
  · obtain ⟨L, y, hy⟩ := exists_rep k Ω (x : Ω)
    exact ⟨L, y, hy.symm⟩
  · obtain ⟨c, hi, hj⟩ := dir k Ω i j
    refine ⟨c, homOfLE hi, homOfLE hj, ?_⟩
    apply Subtype.ext
    exact h

end Alg

section Geo
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

private def tr {L L' : IntermediateField k Ω} (h : L ≤ L') : geom L' p ⟶ geom L p :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)) (by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    congr 3)

private theorem tr_fst {L L' : IntermediateField k Ω} (h : L ≤ L') :
    tr p h ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

private theorem tr_snd {L L' : IntermediateField k Ω} (h : L ≤ L') :
    tr p h ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) :=
  pullback.lift_snd _ _ _

private theorem pj_fst (L : IntermediateField k Ω) :
    LateralTheory.EWeil.StabPf.proj L p ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

private theorem pj_snd (L : IntermediateField k Ω) :
    LateralTheory.EWeil.StabPf.proj L p ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap L Ω)) := pullback.lift_snd _ _ _

private theorem pj_tr {L L' : IntermediateField k Ω} (h : L ≤ L') :
    LateralTheory.EWeil.StabPf.proj L' p ≫ tr p h = LateralTheory.EWeil.StabPf.proj L p := by
  apply pullback.hom_ext
  · rw [Category.assoc, tr_fst, pj_fst, pj_fst]
  · rw [Category.assoc, tr_snd, ← Category.assoc, pj_snd, Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, pj_snd]
    rfl

variable (k Ω) in

private def Gd : (FI k Ω)ᵒᵖ ⥤ Scheme.{0} where
  obj L := geom L.unop.1 p
  map f := tr p (leOfHom f.unop)
  map_id L := by
    apply pullback.hom_ext
    · exact (tr_fst p _).trans (Category.id_comp _).symm
    · refine (tr_snd p _).trans ?_
      refine Eq.trans ?_ (Category.id_comp _).symm
      have e : CommRingCat.ofHom (IntermediateField.inclusion (le_refl L.unop.1)).toRingHom = 𝟙 _ := rfl
      exact (congrArg (fun t => pullback.snd _ _ ≫ Spec.map t) e).trans (by simp)
  map_comp {L L' L''} f g := by
    apply pullback.hom_ext
    · refine (tr_fst p _).trans ?_
      rw [Category.assoc, tr_fst, tr_fst]
    · refine (tr_snd p _).trans ?_
      rw [Category.assoc, tr_snd, ← Category.assoc, tr_snd, Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      rfl

variable (k Ω) in

private def cn : Cone (Gd k Ω p) where
  pt := geom Ω p
  π := { app := fun L => LateralTheory.EWeil.StabPf.proj L.unop.1 p
         naturality := fun L L' f => (Category.id_comp _).trans (pj_tr p (leOfHom f.unop)).symm }

private def bt : FI k Ω := ⟨⊥, inferInstance⟩

section Lim
variable {T : Scheme.{0}} (a : ∀ L : FI k Ω, T ⟶ geom L.1 p)
  (ha : ∀ (L L' : FI k Ω) (h : L.1 ≤ L'.1), a L' ≫ tr p h = a L)

include ha in
private theorem a_snd (L L' : FI k Ω) (h : L.1 ≤ L'.1) :
    a L ≫ pullback.snd _ _ = (a L' ≫ pullback.snd _ _) ≫
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) := by
  rw [← ha L L' h, Category.assoc, tr_snd, Category.assoc]

include ha in
private theorem a_fst (L : FI k Ω) : a L ≫ pullback.fst _ _ = a bt ≫ pullback.fst _ _ := by
  have h : (bt : FI k Ω).1 ≤ L.1 := bot_le
  have e := tr_fst p h
  rw [← ha bt L h, Category.assoc, e]

private def sc : Cone ((Dg k Ω).op ⋙ Scheme.Spec) where
  pt := T
  π := { app := fun L => a L.unop ≫ pullback.snd _ _
         naturality := fun L L' f => (Category.id_comp _).trans (a_snd p a ha L'.unop L.unop (leOfHom f.unop)) }

private def hl [Algebra.IsAlgebraic k Ω] : IsLimit (Scheme.Spec.mapCone (cg k Ω).op) :=
  isLimitOfPreserves Scheme.Spec (cgColim k Ω).op

variable [Algebra.IsAlgebraic k Ω]

private def lf : T ⟶ Spec (CommRingCat.of Ω) := (hl (k := k) (Ω := Ω)).lift (sc p a ha)

private theorem lf_fac (L : FI k Ω) :
    lf p a ha ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 Ω)) = a L ≫ pullback.snd _ _ :=
  (hl (k := k) (Ω := Ω)).fac (sc p a ha) (op L)

private theorem lf_uniq (m : T ⟶ Spec (CommRingCat.of Ω))
    (hm : ∀ L : FI k Ω, m ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 Ω)) = a L ≫ pullback.snd _ _) :
    m = lf p a ha :=
  (hl (k := k) (Ω := Ω)).uniq (sc p a ha) m fun L => hm L.unop

private theorem lf_cond : (a bt ≫ pullback.fst _ _) ≫ p =
    lf p a ha ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap k Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap (bt (k := k) (Ω := Ω)).1 Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (bt (k := k) (Ω := Ω)).1)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [e, ← Category.assoc, lf_fac, Category.assoc, Category.assoc, pullback.condition]

private def gl : T ⟶ geom Ω p := pullback.lift (a bt ≫ pullback.fst _ _) (lf p a ha) (lf_cond p a ha)

private theorem gl_fst : gl p a ha ≫ pullback.fst _ _ = a bt ≫ pullback.fst _ _ := pullback.lift_fst _ _ _

private theorem gl_snd : gl p a ha ≫ pullback.snd _ _ = lf p a ha := pullback.lift_snd _ _ _

private theorem gl_fac (L : FI k Ω) : gl p a ha ≫ LateralTheory.EWeil.StabPf.proj L.1 p = a L := by
  apply pullback.hom_ext
  · rw [Category.assoc, pj_fst, gl_fst]
    exact (a_fst p a ha L).symm
  · rw [Category.assoc, pj_snd, ← Category.assoc, gl_snd, lf_fac]

private theorem gl_uniq (m : T ⟶ geom Ω p) (hm : ∀ L : FI k Ω, m ≫ LateralTheory.EWeil.StabPf.proj L.1 p = a L) :
    m = gl p a ha := by
  apply pullback.hom_ext
  · rw [gl_fst, ← hm bt, Category.assoc, pj_fst]
  · rw [gl_snd]
    refine lf_uniq p a ha _ fun L => ?_
    rw [← hm L, Category.assoc, Category.assoc, pj_snd]

end Lim

private def cnLim [Algebra.IsAlgebraic k Ω] : IsLimit (cn k Ω p) where
  lift s := gl p (fun L => s.π.app (op L)) fun L L' h => s.w (homOfLE (show L ≤ L' from h)).op
  fac s L := gl_fac p (fun L => s.π.app (op L)) (fun L L' h => s.w (homOfLE (show L ≤ L' from h)).op) L.unop
  uniq s m hm := gl_uniq p (fun L => s.π.app (op L)) (fun L L' h => s.w (homOfLE (show L ≤ L' from h)).op) m
    fun L => hm (op L)

private theorem gd_compact (hqc : QuasiCompact p) (L : IntermediateField k Ω) : CompactSpace (geom L p) := by
  haveI : QuasiCompact (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback _ _) hqc
  exact QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L))))

private theorem gd_qs (hqs : QuasiSeparated p) (L : IntermediateField k Ω) : QuasiSeparatedSpace (geom L p) := by
  haveI : QuasiSeparated (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (IsPullback.of_hasPullback _ _) hqs
  exact quasiSeparatedSpace_of_quasiSeparated
    (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L))))

private theorem tr_affine {L L' : IntermediateField k Ω} (h : L ≤ L') : IsAffineHom (tr p h) := by
  have e : Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L)) = Spec.map (CommRingCat.ofHom (algebraMap k L')) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hsq : IsPullback (tr p h) (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L'))))
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap k L))) (v₁₃ := p) ?_ (tr_snd p h)
      (IsPullback.of_hasPullback _ _)
    rw [tr_fst, e]
    exact IsPullback.of_hasPullback _ _
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) hsq.flip (isAffineHom_of_isAffine _)

end Geo

end UpperTheory.Gal.Int.Geo.HeightDescentDirectedColimits

open UpperTheory.Gal.Int.Geo.HeightDescentDirectedColimits in
theorem UpperTheory.Gal.Int.Geo.htDesc_of :
    HtDesc := by
  intro q k Ω _ _ _ _ X p hqc hqs n i y
  obtain ⟨L, z, hz⟩ := (GlobalTheory.T.contCone_of_isLimit_of_qcqs_affine_transitions (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) _ (Gd k Ω p) (cn k Ω p) (cnLim p)
    (fun L => gd_compact p hqc L.unop.1) (fun L => gd_qs p hqs L.unop.1) (fun _ _ f => tr_affine p (leOfHom f.unop)) n).1 y
  exact ⟨L.unop.1, L.unop.2, z, hz⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHtotFin
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem finOfDeg {K : Type} [Field K] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module K (A n)] (hf : ∀ n, FiniteDimensional K (A n)) (N : ℤ)
    (hs : ∀ n, (n < 0 ∨ N < n) → Subsingleton (A n)) :
    FiniteDimensional K (DirectSum ℤ A) := by
  classical
  let S : Finset ℤ := Finset.Icc 0 N
  have hall : ∀ x : DirectSum ℤ A, x ∈ ⨆ n ∈ S, LinearMap.range (DirectSum.lof K ℤ A n) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | of i a =>
      by_cases hi : i ∈ S
      · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ⟨a, rfl⟩)
      · have hout : i < 0 ∨ N < i := by
          simp only [S, Finset.mem_Icc, not_and_or, not_le] at hi
          exact hi
        haveI := hs i hout
        rw [Subsingleton.elim a 0, map_zero]
        exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have htop : (⨆ n ∈ S, LinearMap.range (DirectSum.lof K ℤ A n)) = ⊤ :=
    eq_top_iff.2 (fun x _ => hall x)
  refine Module.finite_def.2 ?_
  rw [← htop]
  refine Submodule.fg_biSup S _ (fun n _ => ?_)
  rw [LinearMap.range_eq_map]
  exact (Module.finite_def.1 (hf n)).map _

theorem UpperTheory.Gal.Int.Geo.htotFin_of :
    DegFin → HtotFin := by
  intro h l _ k _ _ hl X p hp hproj
  obtain ⟨hf, N, hN⟩ := h l k hl p hp hproj
  exact finOfDeg hf N hN
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PMatConj
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem conj_basis {L : Type} [Field L] {M : Type*} [AddCommGroup M] [Module L M]
    (U : Submodule L M) {d : ℕ} (b : Module.Basis (Fin d) L U) (P : GL (Fin d) L) :
    ∃ b' : Module.Basis (Fin d) L U,
      ∀ j, (b' j).1 = ∑ i, (P : Matrix (Fin d) (Fin d) L) i j • (b i).1 := by
  have h1 : (P : Matrix (Fin d) (Fin d) L) * ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) * (P : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let e : U ≃ₗ[L] U := LinearEquiv.ofLinear (Matrix.toLin b b (P : Matrix (Fin d) (Fin d) L))
    (Matrix.toLin b b ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L))
    (by rw [← Matrix.toLin_mul b b b, h1, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul b b b, h2, Matrix.toLin_one])
  refine ⟨b.map e, fun j => ?_⟩
  have h : e (b j) = ∑ i, (P : Matrix (Fin d) (Fin d) L) i j • b i :=
    Matrix.toLin_self b b _ j
  simp [h]

private theorem conj_mat {L : Type} [Field L] {M : Type*} [AddCommGroup M] [Module L M]
    (f : M →ₗ[L] M) {d : ℕ} (x y : Fin d → M) (A P Q : Matrix (Fin d) (Fin d) L) (hPQ : P * Q = 1)
    (hx : ∀ j, f (x j) = ∑ i, A i j • x i) (hy : ∀ j, y j = ∑ i, P i j • x i) (j : Fin d) :
    f (y j) = ∑ i, (Q * A * P) i j • y i := by
  have key : ∀ (B : Matrix (Fin d) (Fin d) L) (j : Fin d),
      ∑ i, B i j • y i = ∑ t, (P * B) t j • x t := by
    intro B j
    simp only [hy, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [key, show P * (Q * A * P) = A * P by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul], hy j]
  simp only [map_sum, map_smul, hx, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]

theorem UpperTheory.Gal.Int.Geo.matConj_of :
    MatConj := by
  intro l _ k _ H Ω _ _ L _ _ θ d ρ P ⟨b, hb⟩
  obtain ⟨b', hb'⟩ := conj_basis _ b P
  refine ⟨b', fun σ j => ?_⟩
  have h1 : (P : Matrix (Fin d) (Fin d) L) * ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [cj_apply, Units.val_mul, Units.val_mul]
  exact conj_mat (galV l H Ω L σ) (fun i => (b i).1) (fun i => (b' i).1) _ _ _ h1 (hb σ) hb' j
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PPieceStab
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.pieceStab_of :
    HopGal → PieceStab := by
  intro hG l _ k _ hl H hfet Ω _ _ L _ _ θ σ x hx
  simp only [piece, Submodule.mem_iInf] at hx ⊢
  intro g
  obtain ⟨d, hd⟩ := hfet g
  have hc := hG l k hl H Ω g d hd σ
  have hxg := hx g
  rw [Module.End.mem_eigenspace_iff] at hxg ⊢
  have e : (LinearMap.baseChange L (hop l H Ω g)) ((galV l H Ω L σ) x)
      = (galV l H Ω L σ) ((LinearMap.baseChange L (hop l H Ω g)) x) := by
    show ((LinearMap.baseChange L (hop l H Ω g)) ∘ₗ (LinearMap.baseChange L (galTot l Ω H.q σ))) x
      = ((LinearMap.baseChange L (galTot l Ω H.q σ)) ∘ₗ (LinearMap.baseChange L (hop l H Ω g))) x
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hc]
  rw [e, hxg, map_smul]
end

