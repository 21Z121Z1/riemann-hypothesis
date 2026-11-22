import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesOfDerivationsKill
section
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin

theorem foldr_iterate_of_kills {A ι : Type} [Zero A] (ds : ι → A → A) (α : ι → ℕ) (c : A)
    (hc : ∀ i, ds i c = 0) (h0 : ∀ i, ds i 0 = 0) (l : List ι) :
    ((∀ i ∈ l, α i = 0) → l.foldr (fun i g => (ds i)^[α i] g) c = c) ∧
    (¬ (∀ i ∈ l, α i = 0) → l.foldr (fun i g => (ds i)^[α i] g) c = 0) := by
  induction l with
  | nil => exact ⟨fun _ => rfl, fun h => absurd (fun i hi => by simp at hi) h⟩
  | cons j l ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [List.foldr_cons, h j (by simp), ih.1 (fun i hi => h i (by simp [hi]))]
      rfl
    · rw [List.foldr_cons]
      by_cases hl : ∀ i ∈ l, α i = 0
      · rw [ih.1 hl]
        have hj : α j ≠ 0 := by
          intro hj
          apply h
          intro i hi
          rcases List.mem_cons.1 hi with rfl | hi
          · exact hj
          · exact hl i hi
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
        rw [hk, Function.iterate_succ_apply, hc j]
        exact Function.iterate_fixed (h0 j) k
      · rw [ih.2 hl]
        exact Function.iterate_fixed (h0 j) _

theorem taylor_const :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A) (c : A), (∀ i, ds i c = 0) → taylor ev (fun i => ⇑(ds i)) c = MvPowerSeries.C (ev c) := by
  intro A B _ _ _ n ev ds c hc
  ext α
  rw [MvPowerSeries.coeff_C]
  change (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp (fun i => ⇑(ds i)) α c) = _
  split_ifs with h
  · subst h
    rw [iterOp_zero]
    simp
  · have : iterOp (fun i => ⇑(ds i)) α c = 0 := by
      refine (foldr_iterate_of_kills (fun i => ⇑(ds i)) α c hc (fun i => map_zero _) _).2 ?_
      intro h'
      apply h
      ext i
      exact h' i (List.mem_finRange i)
    rw [this, map_zero, smul_zero]

end GlobalTheory.FormalOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectNormalisedEqOne
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNorm

theorem tripleFibreProductProjOneThree_comp_fst {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pr13 f ≫ pullback.fst f f = pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f :=
  pullback.lift_fst _ _ _

theorem tripleFibreProductProjOneThree_comp_snd {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pr13 f ≫ pullback.snd f f = pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f :=
  pullback.lift_snd _ _ _

theorem defect_eq_one_of_coboundary {X Y Z : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (hL : L.IsLB)
    (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (z : X ⟶ X)
    (ρ : pullback f f ⟶ pullback f f) (σ : Triple f ⟶ Triple f)
    (h₁ : ρ ≫ pullback.fst f f = pullback.fst f f ≫ z) (h₂ : ρ ≫ pullback.snd f f = pullback.snd f f ≫ z)
    (k₁ : σ ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) =
      pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ ρ)
    (k₂ : σ ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) =
      pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ ρ)
    (g : X ⟶ Z) (U : L.ι → Z.Opens) (s : ∀ i, Γ(Z, U i)ˣ)
    (hN : ∀ (T : Scheme.{0}) (r : T ⟶ pullback f f) (t : T) (i j : L.ι),
      pullback.fst f f (ρ (r t)) ∈ L.U i → pullback.snd f f (ρ (r t)) ∈ L.U j →
      gm (r ≫ ρ) t _ (φ i j) =
        (gm (r ≫ pullback.fst f f ≫ g) t _ (s i))⁻¹ * gm (r ≫ pullback.snd f f ≫ g) t _ (s j))
    (hD : Defect f L φ D) (w : Triple f) : gm σ w ⊤ D = 1 := by
  have c : pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f =
      pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f := pullback.condition
  have k₃ : σ ≫ pr13 f = pr13 f ≫ ρ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, tripleFibreProductProjOneThree_comp_fst, h₁, ← Category.assoc, k₁, Category.assoc, h₁,
        ← Category.assoc, ← Category.assoc, tripleFibreProductProjOneThree_comp_fst]
    · rw [Category.assoc, Category.assoc, tripleFibreProductProjOneThree_comp_snd, h₂, ← Category.assoc, k₂, Category.assoc, h₂,
        ← Category.assoc, ← Category.assoc, tripleFibreProductProjOneThree_comp_snd]
  obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)))
  obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)))
  obtain ⟨k, hk⟩ := exists_chart hL (pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)))
  have e := hD _ σ w i j k hi hj hk
  have p₁ : ρ (pullback.fst (pullback.snd f f) (pullback.fst f f) w) =
      pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w) := congrArg (fun m => m w) k₁.symm
  have p₂ : ρ (pullback.snd (pullback.snd f f) (pullback.fst f f) w) =
      pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w) := congrArg (fun m => m w) k₂.symm
  have p₃ : ρ (pr13 f w) = pr13 f (σ w) := congrArg (fun m => m w) k₃.symm
  have pc : pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)) =
      pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) c.symm
  have q₁ : pullback.fst f f (pr13 f (σ w)) =
      pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) (tripleFibreProductProjOneThree_comp_fst f)
  have q₂ : pullback.snd f f (pr13 f (σ w)) =
      pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) (tripleFibreProductProjOneThree_comp_snd f)
  have a := hN _ (pullback.fst (pullback.snd f f) (pullback.fst f f)) w i j (by rw [p₁]; exact hi)
    (by rw [p₁]; exact hj)
  have b := hN _ (pullback.snd (pullback.snd f f) (pullback.fst f f)) w j k (by rw [p₂, pc]; exact hj)
    (by rw [p₂]; exact hk)
  have d := hN _ (pr13 f) w i k (by rw [p₃, q₁]; exact hi) (by rw [p₃, q₂]; exact hk)
  simp only [← Category.assoc] at a b d
  rw [tripleFibreProductProjOneThree_comp_fst, tripleFibreProductProjOneThree_comp_snd] at d
  rw [← c] at b
  rw [k₁, k₂, k₃, a, b, d, _root_.mul_assoc, mul_inv_cancel_left] at e
  exact mul_eq_right.1 e

theorem defect_normalised : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → ∀ (φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ) (D : Γ(Triple (q ▷ B).left, ⊤)ˣ), NormAlong q P τ φ → Defect (q ▷ B).left P φ D → ∀ w : Triple (q ▷ B).left, gm (rhoW q) w ⊤ D = 1 := by
  intro K _ A A' B _ _ q P τ hP φ D hN hD w
  exact defect_eq_one_of_coboundary (q ▷ B).left P hP φ D (zb A B).left (rhoZ q) (rhoW q) (rhoZ_fst q) (rhoZ_snd q)
    (rhoW_fst q) (rhoW_snd q) (fst A B).left _ (fun i => τ.s fun _ => i) hN hD w

end GlobalTheory.DescNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantNonzeroDifferentials
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

open ReciprocityTheory.ChartRestriction.G.Chart (isTan_iff) in

theorem detGen_apply_ne_zero_of_isDiff : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetGen) (v : Fin (Module.finrank ℚ F) → X.Lie)
    (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
    (∀ j, u.IsDiff (W j) (v j).hom) → W.det ≠ 0 → δ.1 v ≠ 0 := by
  intro F _ _ 𝔠 X L u δ v W hW hdet
  obtain ⟨h1, h2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  have hsm : Smooth X.A.hom := by
    haveI := X.dim
    exact SmoothOfRelativeDimension.smooth (Module.finrank ℚ F) X.A.hom
  obtain ⟨v₀, hv₀, -⟩ := GlobalTheory.exists_lieBasis_of_holUnif X.A L _ u hsm h1 h2
  let b := Serre.Lie.basis X.rm hv₀
  have hsmul : ∀ (c : ℂ) (w : Fin (Module.finrank ℚ F) → ℂ) (x : X.Lie), u.IsDiff w x.hom →
      u.IsDiff (c • w) (c • x).hom := by
    intro c w x h
    have := GlobalTheory.UnifLieBasis.isDiff_smul u ((isTan_iff _).2 x.isTangent) h c
    convert this using 1
    rfl
  have hsum : ∀ a : Fin (Module.finrank ℚ F) → ℂ, u.IsDiff (∑ j, a j • W j) (∑ j, a j • v j).hom := by
    intro a
    rw [Serre.Lie.hom_sum, ← List.prod_ofFn]
    exact (GlobalTheory.UnifLieBasis.isDiff_list_prod u _ _ (fun j ↦ (isTan_iff _).2 (a j • v j).isTangent)
      (fun j ↦ hsmul _ _ _ (hW j))).2
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 := hsum a
    rw [ha] at h0
    have hz : u.IsDiff 0 (0 : X.Lie).hom := by
      rw [Serre.Lie.hom_zero]
      exact GlobalTheory.UnifLieBasis.isDiff_zero u
    have heq : ∑ j, a j • W j = 0 := (h1 _ (0 : X.Lie).isTangent).unique h0 hz
    rw [← Matrix.vecMul_eq_sum] at heq
    by_contra hne
    push_neg at hne
    obtain ⟨i, hi⟩ := hne
    exact hdet (Matrix.exists_vecMul_eq_zero_iff.1 ⟨a, fun h ↦ hi (by rw [h]; rfl), heq⟩)
  haveI : Nonempty (Fin (Module.finrank ℚ F)) := Fin.pos_iff_nonempty.1 Module.finrank_pos
  let B := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, Module.finrank_eq_card_basis b, Fintype.card_fin])
  have hB : (B : Fin (Module.finrank ℚ F) → X.Lie) = v := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hmem : B.det ∈ Submodule.span ℂ {δ.1} := by rw [δ.2]; exact Submodule.mem_top
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hmem
  intro h0
  have h1' := B.det_self
  rw [← ht, hB, AlternatingMap.smul_apply, h0, smul_zero] at h1'
  exact zero_ne_one h1'

end GlobalTheory.LatJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEndOfEighthPowerOfPolAVPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem isDiagEnd_pullback : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}}
    (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (ψ : P'.A.left ⟶ P.A.left)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P u ε → IsGrpPullback P'.A P.A f ψ →
    LBIso P'.L (P.L.pull ψ) → ∃ ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A),
      IsDiagEnd F W P' (f ≫ u) ε' ∧ ∀ E, (ε' E).left ≫ ψ = ψ ≫ (ε E).left := by
  intro g n F W T T' P P' u f φ ε hS hφ hL
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hdiag⟩ := hS
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n _ (zetaAway n) T T' (u ≫ F.s) ((f ≫ u) ≫ F.s) f c
    (by rw [Category.assoc])
  have hc'u : SiegPB c' F.univ (f ≫ u) := GlobalTheory.SiegelPullComp.pb_comp hc hc'
  obtain ⟨ψ, ψ₂, hψ, hsq, hw, -⟩ := hc'
  have hp := hψ.1
  have hφp := hφ.1
  have wa : ∀ a, (φ ≫ (pr a).left) ≫ c.A.hom = P'.A.hom ≫ f := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let pr' : Fin 8 → (P'.A ⟶ c'.A) := fun a =>
    Over.homMk (hp.lift (φ ≫ (pr a).left) P'.A.hom (wa a)) (hp.lift_snd _ _ _)
  have hpr'ψ : ∀ a, (pr' a).left ≫ ψ = φ ≫ (pr a).left := fun a => hp.lift_fst _ _ _
  have push_comp : ∀ {T₁ : Over T'} (x : T₁ ⟶ P'.A) a, pushPt hψ.1.w (x ≫ pr' a) = pushPt hφ.1.w x ≫ pr a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ (pr' a).left) ≫ ψ = (x.left ≫ φ) ≫ (pr a).left
      rw [Category.assoc, hpr'ψ, Category.assoc])
  have pmψ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ c'.A), pushPt hψ.1.w (x * y) = pushPt hψ.1.w x * pushPt hψ.1.w y :=
    fun x y => map_mul (pushHom hψ _) x y
  have pmφ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have injψ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ c'.A}, pushPt hψ.1.w x = pushPt hψ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hψ _ e
  have injφ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hφ _ e
  have hmon : ∀ a, IsMonHom (pr' a) := fun a => by
    haveI := hpr a
    refine isMonHom_of_mul _ fun T₁ x y => injψ ?_
    rw [push_comp, pmψ, push_comp, push_comp, pmφ]
    exact MonObj.mul_comp _ _ _
  have huniv' : ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a := by
    intro T₁ y
    obtain ⟨x₀, hx₀, hu₀⟩ := huniv (Over.mk (T₁.hom ≫ f)) (fun a => pushPt hψ.1.w (y a))
    let x : T₁ ⟶ P'.A := Over.homMk (hφp.lift x₀.left T₁.hom (Over.w x₀)) (hφp.lift_snd _ _ _)
    have hx : pushPt hφ.1.w x = x₀ := Over.OverMorphism.ext (hφp.lift_fst _ _ _)
    have key : ∀ z : T₁ ⟶ P'.A, (∀ a, z ≫ pr' a = y a) ↔ ∀ a, pushPt hφ.1.w z ≫ pr a = pushPt hψ.1.w (y a) :=
      fun z => forall_congr' fun a => ⟨fun h => by rw [← push_comp, h], fun h => injψ (by rw [push_comp, h])⟩
    refine ⟨x, (key x).2 (by rw [hx]; exact hx₀), fun z hz => injφ ?_⟩
    exact (hu₀ _ ((key z).1 hz)).trans hx.symm
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr' ab.1) (pr' ab.2)).left ≫ ψ₂ = φ ≫ (lift (pr ab.1) (pr ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (φ ≫ P.A.hom)) (T' := P'.A)
      (𝟙 P'.A.left) (pr' ab.1) (pr' ab.2) (Z := P.A) φ (pr ab.1) (pr ab.2)
      ((Category.id_comp _).trans (hpr'ψ ab.1)) ((Category.id_comp _).trans (hpr'ψ ab.2)))
  have hbun' : LBIso P'.L (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left)
      (fun ab => W ab.1 ab.2)) := by
    let ε : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
    let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
    let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
    have l0 : (LB.LinComb c.P q ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε
    have l1 : (LB.LinComb c.P (fun ab => φ ≫ q ab) ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB _ ε
    have l2 : (LB.LinComb (c.P.pull ψ₂) q' ε).IsLB :=
      ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c.P.pull ψ₂) (pull_isLB c.isLB ψ₂) q' ε
    have l3 : (LB.LinComb c'.P q' ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε
    have refl1 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
      ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
    have i2 : LBIso (P.L.pull φ) ((LB.LinComb c.P q ε).pull φ) := GlobalTheory.SiegelPullComp.iso_pull φ hbun
    have i3 : LBIso ((LB.LinComb c.P q ε).pull φ) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
      LBIso.chartPull (chartPullOut c.P q ε φ _ fun _ => rfl) (chartPullId _) refl1
    have i4 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb (c.P.pull ψ₂) q' ε) :=
      LBIso.chartPull (chartPullId _)
        (chartPullLinComb c.P ψ₂ q' (fun ab => φ ≫ q ab) ε (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
    have i5 : LBIso (LB.LinComb (c.P.pull ψ₂) q' ε) (LB.LinComb c'.P q' ε) :=
      GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q' ε
    have h1 := pull_isLB P.isLB φ
    have h2 := pull_isLB l0 φ
    exact LBIso.trans P'.isLB h1 l3 hL (LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5)))

  have wε : ∀ E, (φ ≫ (ε E).left) ≫ P.A.hom = P'.A.hom ≫ f := fun E => by
    rw [Category.assoc, Over.w, hφp.w]
  let ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A) := fun E =>
    Over.homMk (hφp.lift (φ ≫ (ε E).left) P'.A.hom (wε E)) (hφp.lift_snd _ _ _)
  have hε'φ : ∀ E, (ε' E).left ≫ φ = φ ≫ (ε E).left := fun E => hφp.lift_fst _ _ _
  let U : Over.mk (P'.A.hom ≫ f) ⟶ P.A := pushPt hφ.1.w (𝟙 P'.A)
  have hUl : U.left = φ := by
    simp [U, pushPt]
  have hpushε : ∀ E, pushPt hφ.1.w (ε' E) = U ≫ ε E := fun E => Over.OverMorphism.ext (by
    show (ε' E).left ≫ φ = U.left ≫ (ε E).left
    rw [hUl, hε'φ])
  have hpushpr : ∀ b, pushPt hψ.1.w (pr' b) = U ≫ pr b := fun b => by
    rw [← push_comp]; simp
  refine ⟨ε', ⟨c', hc'u, pr', hmon, huniv', hbun', fun E a => injψ ?_⟩, hε'φ⟩
  rw [push_comp, hpushε, Category.assoc, hdiag E a]
  change preHom (G := c.A) U _ = pushHom hψ P'.A _
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp_apply, map_zpow]
  congr 1
  exact (hpushpr b).symm

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBas
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section General

variable {A : Type} [Ring A]

theorem span_mul_mem {S : Set A} (h : ∀ s ∈ S, ∀ y, s * y ∈ Ideal.span S) {x : A} (hx : x ∈ Ideal.span S) (y : A) :
    x * y ∈ Ideal.span S := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx y
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul r x _ ih => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ ih

theorem span_map_mem (f : A →+* A) {S : Set A} (h : ∀ s ∈ S, f s ∈ Ideal.span S) {x : A} (hx : x ∈ Ideal.span S) :
    f x ∈ Ideal.span S := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul r x _ ih => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ ih

theorem sup_mul_mem {I K : Ideal A} (hI : ∀ x ∈ I, ∀ y, x * y ∈ I) (hK : ∀ x ∈ K, ∀ y, x * y ∈ K) {x : A}
    (hx : x ∈ I ⊔ K) (y : A) : x * y ∈ I ⊔ K := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [add_mul]
  exact add_mem (Ideal.mem_sup_left (hI a ha y)) (Ideal.mem_sup_right (hK b hb y))

theorem sup_map_mem (f : A →+* A) {I K : Ideal A} (hI : ∀ x ∈ I, f x ∈ I) (hK : ∀ x ∈ K, f x ∈ K) {x : A}
    (hx : x ∈ I ⊔ K) : f x ∈ I ⊔ K := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact add_mem (Ideal.mem_sup_left (hI a ha)) (Ideal.mem_sup_right (hK b hb))

end General

section Filt

variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J)

theorem fil_anti' {m n : ℕ} (h : m ≤ n) : fil δ n ≤ fil δ m :=
  Ideal.span_mono fun _ ⟨l, h1, h2, h3⟩ ↦ ⟨l, h1, h.trans h2, h3⟩

theorem fil_mul_mem' {m n : ℕ} {a b : B} (ha : a ∈ fil δ m) (hb : b ∈ fil δ n) : a * b ∈ fil δ (m + n) := by
  have key : fil δ m * fil δ n ≤ fil δ (m + n) := by
    rw [fil, fil, Ideal.span_mul_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨x, ⟨l, hl, hs, rfl⟩, y, ⟨l', hl', hs', rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨l ++ l', fun p hp ↦ ?_, ?_, ?_⟩
    · rcases List.mem_append.1 hp with hp | hp
      exacts [hl p hp, hl' p hp]
    · simp only [List.map_append, List.sum_append]; omega
    · simp only [List.map_append, List.prod_append]
  exact key (Ideal.mul_mem_mul ha hb)

end Filt

section Main

variable (R : Type) [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

def relGen : Set (DR R B) :=
  {x | ∃ n : ℕ, ∃ a ∈ J, x = ι1 (D R B (δ.dpow (n + 1) a) - δ.dpow n a • D R B a)}

theorem rel_eq_span : rel R δ = Ideal.span (relGen R δ) := rfl

theorem rel_mul_mem {x : DR R B} (hx : x ∈ rel R δ) (y : DR R B) : x * y ∈ rel R δ := by
  rw [rel_eq_span] at hx ⊢
  refine span_mul_mem (fun s hs y ↦ ?_) hx y
  obtain ⟨n, a, ha, rfl⟩ := hs
  rw [ι_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, a, ha, rfl⟩)

theorem sgn_mem_rel {x : DR R B} (hx : x ∈ rel R δ) : sgn x ∈ rel R δ := by
  rw [rel_eq_span] at hx ⊢
  refine span_map_mem (sgn : DR R B →ₐ[B] DR R B).toRingHom (fun s hs ↦ ?_) hx
  obtain ⟨n, a, ha, rfl⟩ := hs
  change sgn (ι1 _) ∈ _
  rw [sgn_ι]
  exact neg_mem (Ideal.subset_span ⟨n, a, ha, rfl⟩)

theorem filSpan_mul_mem (n : ℕ) {x : DR R B} (hx : x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n))
    (y : DR R B) : x * y ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n) := by
  refine span_mul_mem (fun s hs y ↦ ?_) hx y
  obtain ⟨b, hb, rfl⟩ := hs
  rw [Algebra.commutes]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, hb, rfl⟩)

theorem filSpan_sgn_mem (n : ℕ) {x : DR R B} (hx : x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n)) :
    sgn x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n) := by
  refine span_map_mem (sgn : DR R B →ₐ[B] DR R B).toRingHom (fun s hs ↦ ?_) hx
  obtain ⟨b, hb, rfl⟩ := hs
  change sgn (algebraMap B _ b) ∈ _
  rw [AlgHom.commutes]
  exact Ideal.subset_span ⟨b, hb, rfl⟩

theorem filSpan_smul_mem (m n : ℕ) {b : B} (hb : b ∈ fil δ m) {x : DR R B}
    (hx : x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n)) :
    b • x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ (m + n)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [Algebra.smul_def, ← map_mul]
    exact Ideal.subset_span ⟨b * c, fil_mul_mem' δ hb hc, rfl⟩
  | zero => simp
  | add x z _ _ hx hz => rw [smul_add]; exact add_mem hx hz
  | smul r x _ ih =>
    rw [smul_eq_mul, Algebra.smul_def, ← mul_assoc, Algebra.commutes b r, mul_assoc, ← Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ ih

theorem rel_filDR_properties :
    (∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) ∧ (∀ x ∈ rel R δ, sgn x ∈ rel R δ) ∧
    (∀ n, ∀ x ∈ filDR R δ n, ∀ y, x * y ∈ filDR R δ n) ∧ (∀ n, ∀ x ∈ filDR R δ n, sgn x ∈ filDR R δ n) ∧
    filDR R δ 0 = ⊤ ∧ (∀ m n, m ≤ n → filDR R δ n ≤ filDR R δ m) ∧
    ∀ m n, ∀ b ∈ fil δ m, ∀ x ∈ filDR R δ n, b • x ∈ filDR R δ (m + n) := by
  refine ⟨fun x hx y ↦ rel_mul_mem R δ hx y, fun x hx ↦ sgn_mem_rel R δ hx, fun n x hx y ↦ ?_, fun n x hx ↦ ?_,
    ?_, fun m n h ↦ ?_, fun m n b hb x hx ↦ ?_⟩
  · exact sup_mul_mem (fun x hx y ↦ filSpan_mul_mem R δ n hx y) (fun x hx y ↦ rel_mul_mem R δ hx y) hx y
  · exact sup_map_mem (sgn : DR R B →ₐ[B] DR R B).toRingHom (fun x hx ↦ filSpan_sgn_mem R δ n hx)
      (fun x hx ↦ sgn_mem_rel R δ hx) hx
  · refine (Ideal.eq_top_iff_one _).2 (Ideal.mem_sup_left (Ideal.subset_span ⟨1, ?_, map_one _⟩))
    rw [fil_zero_eq_top]; trivial
  · exact sup_le_sup_right (Ideal.span_mono (Set.image_mono (fil_anti' δ h))) _
  · obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine add_mem (Ideal.mem_sup_left (filSpan_smul_mem R δ m n hb ha)) (Ideal.mem_sup_right ?_)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hc

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler in

theorem rel_eq_bot_of_map (I : Ideal R) (κ : DividedPowers I) (h : IsDPMorphism κ δ (algebraMap R B))
    (hJ : J ≤ I.map (algebraMap R B)) : rel R δ = ⊥ := by
  have hD := GlobalTheory.CrysConn.isDPDer_of_map h hJ (D R B)
  rw [rel, Ideal.span_eq_bot]
  rintro _ ⟨n, a, ha, rfl⟩
  rw [hD n a ha, sub_self, map_zero]

end Main

theorem rel_two_sided_and_bot :
    (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J),
      (∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) ∧ (∀ x ∈ rel R δ, sgn x ∈ rel R δ) ∧
      (∀ n, ∀ x ∈ filDR R δ n, ∀ y, x * y ∈ filDR R δ n) ∧ (∀ n, ∀ x ∈ filDR R δ n, sgn x ∈ filDR R δ n) ∧
      filDR R δ 0 = ⊤ ∧ (∀ m n, m ≤ n → filDR R δ n ≤ filDR R δ m) ∧
      ∀ m n, ∀ b ∈ fil δ m, ∀ x ∈ filDR R δ n, b • x ∈ filDR R δ (m + n)) ∧
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (I : Ideal R)
      (κ : DividedPowers I), IsDPMorphism κ δ (algebraMap R B) → J ≤ I.map (algebraMap R B) → rel R δ = ⊥ :=
  ⟨fun R _ _ _ _ _ δ ↦ rel_filDR_properties R δ, fun R _ _ _ _ _ δ I κ h hJ ↦ rel_eq_bot_of_map R δ I κ h hJ⟩

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveCartierIdealSheafLeOfClosedPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effectiveCartier_idealSheaf_le_of_closedPoints : ∀ (X : Scheme.{0}) [CompactSpace X] (D : EffCartierData X) (K : X.IdealSheafData), (∀ x : X, IsClosed ({x} : Set X) → ∃ (W : X.affineOpens) (i : D.ι) (h : W.1 ≤ D.U i), x ∈ W.1 ∧ resG X h (D.f i) ∈ K.ideal W) → D.idealSheaf ≤ K := by
  first | exact @GlobalTheory.EffCartierData.idealSheaf_le_of_closedPoints | exact GlobalTheory.EffCartierData.idealSheaf_le_of_closedPoints | (intros; apply GlobalTheory.EffCartierData.idealSheaf_le_of_closedPoints <;> assumption)
end

