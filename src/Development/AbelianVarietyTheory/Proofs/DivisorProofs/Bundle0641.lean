import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralReducingToMvPowerSeriesSubst
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace Katz

theorem red_subst : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (u' : σ → MvPowerSeries τ k),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, Red p (u i) (u' i)) →
    (∀ (f : MvPowerSeries (σ) (Fr p k)) f', Red p f f' → Red p (subst u f) (subst u' f')) ∧
    ∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c →
      subst u f ∈ intBy p k τ c := by
  intro p _ k _ _ _ σ τ _ u u' hu0 hu
  have hinj : Function.Injective (algebraMap (WittVector p k) (Fr p k)) :=
    IsFractionRing.injective _ _
  have hu1 : ∀ i (α : τ →₀ ℕ), ∃ w : WittVector p k, coeff α (u i) = algebraMap _ (Fr p k) w ∧
      WittVector.constantCoeff w = coeff α (u' i) := hu
  choose U hU using hu1
  let V : σ → MvPowerSeries τ (WittVector p k) := U
  have hV : ∀ i α, coeff α (V i) = U i α := fun _ _ => rfl
  have hmap : u = fun i => map (algebraMap (WittVector p k) (Fr p k)) (V i) := by
    funext i; ext α; rw [coeff_map, hV, (hU i α).1]
  have hmap' : u' = fun i => map (WittVector.constantCoeff (p := p) (R := k)) (V i) := by
    funext i; ext α; rw [coeff_map, hV, (hU i α).2]
  have hV0 : ∀ i, constantCoeff (V i) = 0 := by
    intro i
    apply hinj
    rw [map_zero, ← hu0 i, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      hV, (hU i 0).1]
  have hVs : HasSubst V := hasSubst_of_constantCoeff_zero hV0
  refine ⟨?_, ?_⟩
  · intro f f' hf
    have hf1 : ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) w ∧
        WittVector.constantCoeff w = coeff α f' := hf
    choose F hF using hf1
    let G : MvPowerSeries σ (WittVector p k) := F
    have e1 : f = map (algebraMap (WittVector p k) (Fr p k)) G := by
      ext α; rw [coeff_map]; exact (hF α).1
    have e2 : f' = map (WittVector.constantCoeff (p := p) (R := k)) G := by
      ext α; rw [coeff_map]; exact (hF α).2.symm
    rw [e1, e2, hmap, hmap', ← map_subst hVs, ← map_subst hVs]
    intro α
    exact ⟨coeff α (subst V G), by rw [coeff_map], by rw [coeff_map]⟩
  · intro c f hf
    have hf1 : ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) (c * w) := hf
    choose F hF using hf1
    let G : MvPowerSeries σ (WittVector p k) := F
    have e1 : f = algebraMap (WittVector p k) (Fr p k) c •
        map (algebraMap (WittVector p k) (Fr p k)) G := by
      ext α; rw [coeff_smul, coeff_map, hF α, map_mul]; rfl
    rw [e1, hmap, subst_smul (hVs.map _), ← map_subst hVs]
    intro α
    exact ⟨coeff α (subst V G), by rw [coeff_smul, coeff_map, map_mul]⟩

end Katz

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeQuotientCorrespondenceOfTorsionTranspor
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
open IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.WpFam.TrIs

theorem main : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → IsTr ι Λ₀ Λ₁ (Tr t) := by
  intro K _ _ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT
  obtain ⟨_, _, _, hL0, ⟨𝔞, h𝔞, hL1⟩, _, _, _⟩ := hT
  obtain ⟨hsub, _, hleft, hright⟩ := GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties K t
  have hA : ∀ y : Af K, y ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (y v) ≤ 1 := fun y => GlobalTheory.Idele.mem_adelicIdeal_one_iff
  have hone : ∀ x : K, x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      algebraMap K (Af K) x ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x =>
    (GlobalTheory.Idele.algebraMap_mem_adelicIdeal (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) x).symm
  have hmem𝔞 : ∀ a' : K, a' ∈ 𝔞 ↔ (t : Af K) * algebraMap K (Af K) a' ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a'
    rw [h𝔞, hA]
  have hL0' : ∀ z, z ∈ Λ₀.lattice ↔ z ∈ ι '' ((1 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL0 z
  have hL1' : ∀ z, z ∈ Λ₁.lattice ↔ z ∈ ι '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL1 z
  have h0 : ∀ a : K, ι a ∈ Λ₀.lattice ↔ a ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a
    rw [hL0']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← ι.injective e]
    · intro h; exact ⟨a, h, rfl⟩
  have h1 : ∀ a' : K, ι a' ∈ Λ₁.lattice ↔ a' ∈ 𝔞 := by
    intro a'
    rw [hL1']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← ι.injective e]
    · intro h; exact ⟨a', h, rfl⟩
  have hTr : ∀ x x' : K, Tr t x x' ↔ (t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x x' => (hA _).symm
  refine ⟨hsub, ?_, ?_, hleft, hright, ?_, ?_⟩
  · intro x x' h
    have hd := (hTr x x').1 h
    rw [h0, h1, hone, hmem𝔞]
    constructor
    · intro hx
      have := add_mem hd hx
      rwa [sub_add_cancel] at this
    · intro hx
      have := sub_mem hx hd
      rwa [sub_sub_cancel] at this
  · intro x x' hx hx'
    rw [hTr]
    exact sub_mem ((hmem𝔞 x').1 ((h1 x').1 hx')) ((hone x).1 ((h0 x).1 hx))
  · intro z hz
    obtain ⟨k, -, e⟩ := (hL0' z).1 hz
    exact ⟨k, e⟩
  · intro z hz
    obtain ⟨k, -, e⟩ := (hL1' z).1 hz
    exact ⟨k, e⟩

end GlobalTheory.WpFam.TrIs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullCubicalOfGenericOfExt
section
noncomputable section

namespace GlobalTheory.ChartCubExt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Exist.CubicalExtension

def ExtendGenAt (V K : Type) [CommRing V] [Field K] [Algebra V K] : Prop :=
  ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (eA : Sp K ⟶ pullback G.hom (spMap (algebraMap V K))),
      eA ≫ pullback.fst G.hom (spMap (algebraMap V K)) = spMap (algebraMap V K) ≫ eSec G →
    ∀ (N : RigLB G) (r : LB.Gen (N.L.pull (pullback.fst G.hom (spMap (algebraMap V K))))), r.IsGen →
    LB.Gen.Corr N.L _ _ _ _ (LB.pullGen N.L _ _ r eA) (LB.pullGen N.L _ _ N.rig (spMap (algebraMap V K))) →
    ∃ r' : LB.Gen N.L, r'.IsGen ∧ LB.genPull N.L r' (pullback.fst G.hom (spMap (algebraMap V K))) = r

section Group

variable {T K : Type} [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K]

theorem isPullCubical_of_generic_of_ext (hE : ExtendGenAt T K) {S : Scheme.{0}} {G₀ : Over S} {G : Over (Sp T)}
    {GK : Over (Sp K)} [GrpObj G₀] [IsCommMonObj G₀] [GrpObj G] [IsCommMonObj G] [GrpObj GK] [IsCommMonObj GK]
    (hG : IsSemiAbelian G) {L₀ : RigLB G₀} {L : RigLB G} {LK : RigLB GK} (c₀ : CubicalStr G₀ L₀)
    (c : CubicalStr G L) (cK : CubicalStr GK LK) (n : CubeMap G G₀) (m : CubeMap GK G) (m' : CubeMap GK G₀)
    (hp : IsPullback m.F GK.hom G.hom (spMap (algebraMap T K))) (he : m.e = spMap (algebraMap T K))
    (h₁ : m'.F = m.F ≫ n.F) (h₂ : m'.F3 = m.F3 ≫ n.F3) (h₃ : m'.e = m.e ≫ n.e)
    (H' : m.IsPullCubical cK c) (H'' : m'.IsPullCubical cK c₀) : n.IsPullCubical c c₀ := by
  obtain ⟨F, F3, e, he', hp'⟩ := m'
  dsimp only at h₁ h₂ h₃
  subst h₁ h₂ h₃
  rw [isPullCubical_iff] at H' H'' ⊢
  obtain ⟨w', g', r', q'⟩ := H'
  obtain ⟨w'', g'', r'', q''⟩ := H''
  have := hG.smooth
  have a₁ : eSec G ≫ G.hom = 𝟙 _ := Over.w η[G]
  have a₂ : eSec GK ≫ GK.hom = 𝟙 _ := Over.w η[GK]
  obtain ⟨κ, κ', hκ, hκ'⟩ : ∃ (κ : pullback G.hom (spMap (algebraMap T K)) ⟶ GK.left)
      (κ' : GK.left ⟶ pullback G.hom (spMap (algebraMap T K))),
      κ ≫ m.F = pullback.fst G.hom (spMap (algebraMap T K)) ∧ κ' ≫ κ = 𝟙 _ :=
    ⟨hp.isoPullback.inv, hp.isoPullback.hom, hp.isoPullback_inv_fst, hp.isoPullback.hom_inv_id⟩
  have hj : κ' ≫ pullback.fst G.hom (spMap (algebraMap T K)) = m.F := by rw [← hκ, ← Category.assoc, hκ', Category.id_comp]
  obtain ⟨r, hr, vr⟩ := exists_quot_of_isos L₀.isLB L.isLB LK.isLB w' w'' g' g'' κ (pullback.fst G.hom (spMap (algebraMap T K))) hκ
  obtain ⟨ρ, hρ, vρ⟩ := exists_quot_of_gens n.e_comm L₀.rig L.rig L₀.rigGen L.rigGen
  have heA : (eSec GK ≫ κ') ≫ pullback.fst G.hom (spMap (algebraMap T K)) = spMap (algebraMap T K) ≫ eSec G := by
    rw [Category.assoc, hj, m.e_comm, he]
  have heA' : (eSec GK ≫ κ') ≫ pullback.fst G.hom (spMap (algebraMap T K)) = m.e ≫ eSec G := by
    rw [Category.assoc, hj, m.e_comm]
  have heκ : (eSec GK ≫ κ') ≫ κ = eSec GK := by rw [Category.assoc, hκ', Category.comp_id]
  obtain ⟨w, hw, hwr⟩ := hE G hG (eSec GK ≫ κ') heA
    ⟨LB.div (L₀.L.pull n.F) L.L, ρ, LB.isLB_div (pull_isLB L₀.isLB _) L.isLB, hρ⟩ r hr (by
      intro J J' _ _ hJ
      obtain rfl : J = J' := funext fun _ => hJ PUnit.unit PUnit.unit heA
      refine unit_ext fun y hy => ?_
      refine (gm_res _ y _ hy _).trans (Eq.trans ?_ (gm_res _ y _ hy _).symm)
      refine (gm_pullGen _ _ _ r _ (𝟙 _) y J hy.1).trans (Eq.trans ?_ (gm_pullGen _ _ _ ρ _ (𝟙 _) y J hy.2).symm)
      obtain ⟨k, hk⟩ := exists_chart LK.isLB (eSec GK y)
      have hm := (mem_qchart (j := (eSec GK ≫ κ') ≫ pullback.fst G.hom (spMap (algebraMap T K))) (a := (J PUnit.unit).1 PUnit.unit)
        (i := (J PUnit.unit).2)).1 hy.1
      have hm' := hm
      have hm'' := hm
      rw [heA'] at hm'
      rw [Category.assoc, hj] at hm''
      have e₁ := vr _ (eSec GK ≫ κ') y _ _ k hm.1 hm.2 (by
        show ((eSec GK ≫ κ') ≫ κ) y ∈ _
        rw [heκ]; exact hk)
      have e₂ := vρ _ m.e y _ _ hm'.1 hm'.2
      have e₃ := r'' _ (𝟙 _) y (fun _ => (J PUnit.unit).1 PUnit.unit) (fun _ => k) (fun _ => hm''.1) (fun _ => hk)
      have e₄ := r' _ (𝟙 _) y (fun _ => (J PUnit.unit).2) (fun _ => k) (fun _ => hm''.2) (fun _ => hk)
      rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at e₃ e₄
      rw [heκ] at e₁
      rw [e₃, e₄, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one] at e₂
      rw [Category.id_comp, Category.id_comp]
      refine e₁.trans (e₂.symm.trans ?_)
      rw [he]
      rfl)
  have tri : Tri (L := L₀.L) (L' := L.L) (F := n.F) w w' w'' := by
    intro Y f y a i k ha hi hk
    have p₁ : pullback.fst G.hom (spMap (algebraMap T K)) (κ' (f y)) = m.F (f y) := congrArg (fun g => g (f y)) hj
    have p₂ : κ (κ' (f y)) = f y := congrArg (fun g => g (f y)) hκ'
    have ha' : n.F (pullback.fst G.hom (spMap (algebraMap T K)) (κ' (f y))) ∈ L₀.L.U a := by rw [p₁]; exact ha
    have hi' : pullback.fst G.hom (spMap (algebraMap T K)) (κ' (f y)) ∈ L.L.U i := by rw [p₁]; exact hi
    have e₁ := vr _ (f ≫ κ') y a i k ha' hi' (by
      show κ (κ' (f y)) ∈ _
      rw [p₂]; exact hk)
    have hy : (f ≫ κ') y ∈ qchart L₀.L L.L n.F (pullback.fst G.hom (spMap (algebraMap T K))) a i := mem_qchart.2 ⟨ha', hi'⟩
    have e₂ : gm (f ≫ κ') y (qchart L₀.L L.L n.F (pullback.fst G.hom (spMap (algebraMap T K))) a i) (r.s (fun _ => (fun _ => a, i))) =
        gw (L := L₀.L) (L' := L.L) (F := n.F) w ((f ≫ κ') ≫ pullback.fst G.hom (spMap (algebraMap T K))) y a i := by
      rw [← hwr]
      exact (gm_res _ y _ hy _).trans (gm_pull (f ≫ κ') (pullback.fst G.hom (spMap (algebraMap T K))) y
        ((L₀.L.pull n.F).U (fun _ => a) ⊓ L.L.U i) ⟨mem_pull.2 ha', hi'⟩ _)
    rw [e₂, Category.assoc, Category.assoc, hj, hκ', Category.comp_id] at e₁
    rw [e₁, inv_mul_cancel_right]
  refine ⟨w, (isGen_iff _).1 hw, ?_, ?_⟩
  · refine pmaps_of_tri tri LK.isLB (fun _ => n.e_comm) (fun _ => m.e_comm) r' r'' (𝟙 _) ?_
    rw [Category.id_comp, he]
    exact app_injective_generic (p := 𝟙 _) (q := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
  · have : Flat (G3 G).hom := by
      show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
      infer_instance
    let P : Over (Sp K) := Over.mk (pullback.snd (G3 G).hom (spMap (algebraMap T K)))
    let x : Fin 3 → (P ⟶ GK) := fun i => Over.homMk
      (hp.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact pullback.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ m.F = pullback.fst _ _ ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G3 GK := lift (x 0) (lift (x 1) (x 2))
    have hl : l.left ≫ m.F3 = pullback.fst (G3 G).hom (spMap (algebraMap T K)) := hom_ext_triple _ fun i => by
      have : l ≫ x3 GK i = x i := by fin_cases i <;> simp [l, x3]
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, this, hx]
    refine pmaps_of_tri tri LK.isLB (fun I => n.psum_comm I.down) (fun I => m.psum_comm I.down) q' q'' l.left ?_
    rw [hl]
    exact app_injective_generic (IsPullback.of_hasPullback _ _)

end Group

end GlobalTheory.ChartCubExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAppEqBialgHomKernelIdealOfIdempotents
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

theorem ker_app_eq_kerIdeal_of_idempotents (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]
    (G : PDivGroup p k) (u v : G ⟶ G) (huv : u + v = 𝟙 G) (h1 : u ≫ v = 0) (_h2 : v ≫ u = 0)
    (n : ℕ) : RingHom.ker (u.app n) = kerIdeal (v.app n) := by
  apply le_antisymm
  · intro a ha
    rw [RingHom.mem_ker] at ha
    let x := Ideal.Quotient.mkₐ k (kerIdeal (v.app n))
    have hv : ∀ c, x (v.app n c) = algebraMap k _ (counit c) :=
      (kerIdeal_le_ker_iff (v.app n) x).1 fun b hb => by
        rw [RingHom.mem_ker]
        exact Ideal.Quotient.eq_zero_iff_mem.2 hb
    let P := (ptsPush (G.A n) (x : G.A n →ₐ[k] _)).comp toPts
    have hP : P (Hom.conv v n) = 1 := WithConv.ofConv_injective (AlgHom.ext fun c => by
      change x (v.app n c) = _
      rw [hv]
      simp)
    have e : P (Hom.conv (u + v) n) = P (Hom.conv u n) := by
      rw [add_conv, map_mul, hP, mul_one]
    rw [huv] at e
    have e' := congrArg (fun y => y.ofConv a) e
    change x a = x (u.app n a) at e'
    rw [ha, map_zero] at e'
    exact Ideal.Quotient.eq_zero_iff_mem.1 e'
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e := congrArg (fun f : G ⟶ G => Hom.app f n b) h1
    change u.app n (v.app n b) = (1 : WithConv (G.A n →ₐc[k] G.A n)).ofConv b at e
    have hb' : counit (R := k) b = 0 := hb
    refine Eq.trans e ?_
    simp [hb']

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCocycleSubChernClassCoboundaryStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCocycle_sub_chernClass_coboundary : ∀ (q : ℕ) [NeZero q] (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v) → ∀ (C : Shv ℤ) (a : Cocycle ((chains ℤ).obj E) (sgl C) 1) (w : Cocycle (sgl C) (res ℤ (twZ q)) 1), (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → Sec.map (w.1.v 0 1 (zero_add 1)) (ev a.1 1 0 (by simp) U x) = Sec.map ((res ℤ (twZ q)).d 0 1) (Sec.map φ (unitSec v))) → CohomologyClass.mk (zcomp a w rfl) = restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  first
  | exact @GlobalTheory.EtC.KumPic.Cobd.cobd
  | exact GlobalTheory.EtC.KumPic.Cobd.cobd
  | (intros; apply GlobalTheory.EtC.KumPic.Cobd.cobd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectSectionResStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefectSection_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  first
  | exact @GlobalTheory.EtC.RedChern.defectSec_res
  | exact GlobalTheory.EtC.RedChern.defectSec_res
  | (intros; apply GlobalTheory.EtC.RedChern.defectSec_res <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectEqOfPowEqStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerSplittingDefect_eq_of_pow_eq : ∀ (q : ℕ) [NeZero q] (κ : twZ q ⟶ Gm), (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u) → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), κ ≫ φ = resι ℤ (twZ q) → ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v' := by
  first
  | exact @GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq
  | exact GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq
  | (intros; apply GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectGlueQthRootsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerSplittingDefect_glue_qthRoots : ∀ (q : ℕ) [NeZero q] (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v') → ∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v := by
  first
  | exact @GlobalTheory.EtC.KumPic.DvGlue.glue
  | exact GlobalTheory.EtC.KumPic.DvGlue.glue
  | (intros; apply GlobalTheory.EtC.KumPic.DvGlue.glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDifferenceMulRootOfUnityStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerSplittingDifference_mul_rootOfUnity : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm),
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
    ∀ φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0,
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) →
    ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ (v ω : (Γ(U, ⊤))ˣ), ω ^ q = 1 →
      Sec.map φ (unitSec (ω * v)) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U (ω * v)) =
        Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v) := by
  first | (exact @GlobalTheory.EtC.kumDiff_mul_rootOfUnity) | (exact GlobalTheory.EtC.kumDiff_mul_rootOfUnity) | (intros; apply GlobalTheory.EtC.kumDiff_mul_rootOfUnity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingObstructionBocksteinAdd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem Bock_add : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (x x' : HO1 s') (z z' : HO2 s₀), Bock h h₀ t x z → Bock h h₀ t x' z' → Bock h h₀ t (x + x') (z + z') := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ x x' z z'
  rintro ⟨f, w, hd, ⟨c, hc, hcx⟩, ⟨e, he, hez⟩⟩ ⟨f', w', hd', ⟨c', hc', hcx'⟩, ⟨e', he', hez'⟩⟩
  refine ⟨f + f', w + w', by rw [map_add, hd, hd', smul_add], ⟨c + c', fun p q a ↦ ?_, ?_⟩,
    ⟨e + e', fun p q r a b ↦ ?_, ?_⟩⟩
  · simp only [Submodule.coe_add, Pi.add_apply, hc, hc', map_add]
  · rw [map_add, hcx, hcx', map_add]
  · simp only [Submodule.coe_add, Pi.add_apply, he, he', map_add]
  · rw [map_add, hez, hez', map_add]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairTransferStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_pullback_pair_transfer : ∀ (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X), Q₁.IsLB → Q₂.IsLB → LBIso Q₁ Q₂ → LBIso (Q₁.pull m) (Q₁.pull m') → LBIso (Q₂.pull m) (Q₂.pull m') := by
  first | (exact @GlobalTheory.PullIsoCongr.isocongr) | (exact GlobalTheory.PullIsoCongr.isocongr) | (intros; apply GlobalTheory.PullIsoCongr.isocongr  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitComponentMulMemStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_mul_preimage_of_mem_unitComponent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (η[G]).left (G.hom y) ∈ U → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  first | exact @GlobalTheory.mem_unitComponent_mul_mem | exact GlobalTheory.mem_unitComponent_mul_mem | (intros; apply GlobalTheory.mem_unitComponent_mul_mem <;> assumption)
end

