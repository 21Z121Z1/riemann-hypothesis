import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceInfKerLe
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem lvlIdem_apply_of_mem_eig {Γ V : Type} [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (x : V) (hx : x ∈ eig ρ Hb lam) :
    ρ.asAlgebraHom (Formalism.L2.DIV.lvlIdem Hb lam) x = x := by
  classical
  rw [mem_eig] at hx
  have hc : (Nat.card Hb : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold Formalism.L2.DIV.lvlIdem
  rw [map_sum, LinearMap.sum_apply]
  simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, hx, smul_smul]
  have e1 : ∀ h : Hb, (Nat.card Hb : ℂ)⁻¹ * ((lam h⁻¹ : ℂˣ) : ℂ) * ((lam h : ℂˣ) : ℂ) = (Nat.card Hb : ℂ)⁻¹ := fun h => by
    rw [mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]
  simp only [e1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem finrank_eig_inf_ker_le : ∀ (Γ V : Type) [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (H : Fin 2 → Subgroup Γ) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ Γ) (b : Fin 2 → MonoidAlgebra ℂ Γ) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ (H k) (n k)) → (∀ k, (n k : ℝ) * Nat.card (H k) ≤ c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) → (∀ k, b k * b k = b k) → (∀ k, b k * Formalism.L2.DIV.lvlIdem Hb lam = Formalism.L2.DIV.lvlIdem Hb lam * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff 1 = (s k : ℂ) / (Nat.card Hb : ℂ)) → (finrank ℂ (eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by
  intro Γ V _ _ _ _ _ ρ Hb lam H n e b s c hemb hcard hidem hcomm he hsupp hcoeff
  set p := Formalism.L2.DIV.lvlIdem Hb lam with hp
  set W : Submodule ℂ V := eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) with hW
  let f : W →ₗ[ℂ] LinearMap.range (ρ.asAlgebraHom (b 0 * p)) × LinearMap.range (ρ.asAlgebraHom (b 1 * p)) :=
    ((ρ.asAlgebraHom (b 0 * p)).rangeRestrict.comp W.subtype).prod
      ((ρ.asAlgebraHom (b 1 * p)).rangeRestrict.comp W.subtype)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hxe, hxk⟩ hx0
    have h0 : ρ.asAlgebraHom (b 0 * p) x = 0 := by
      have := congrArg (fun z => ((z.1 : _) : V)) hx0; simpa [f] using this
    have h1 : ρ.asAlgebraHom (b 1 * p) x = 0 := by
      have := congrArg (fun z => ((z.2 : _) : V)) hx0; simpa [f] using this
    have hpx : ρ.asAlgebraHom p x = x := lvlIdem_apply_of_mem_eig ρ Hb lam x hxe
    have hb : ∀ k, ρ.asAlgebraHom (b k) x = ρ.asAlgebraHom (b k * p) x := fun k => by
      rw [map_mul, Module.End.mul_apply, hpx]
    have hb0 : ρ.asAlgebraHom (b 0) x = 0 := (hb 0).trans h0
    have hb1 : ρ.asAlgebraHom (b 1) x = 0 := (hb 1).trans h1
    have hek : ρ.asAlgebraHom e x = 0 := hxk
    have hx1 : x = ρ.asAlgebraHom (1 - e) x := by
      rw [map_sub, map_one, LinearMap.sub_apply, hek, sub_zero]; rfl
    have : x = 0 := by
      rw [hx1, he, map_sub, map_add, map_mul]
      simp [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, hb0, hb1]
    exact Subtype.ext this
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hdim
  have hbnd : ∀ k, (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤
      c * s k * finrank ℂ (eig ρ Hb lam) := by
    intro k
    have hid : b k * p * (b k * p) = b k * p := by
      calc b k * p * (b k * p) = b k * (p * b k) * p := by simp only [mul_assoc]
        _ = b k * (b k * p) * p := by rw [hcomm k]
        _ = (b k * b k) * (p * p) := by simp only [mul_assoc]
        _ = b k * p := by rw [hidem k, Formalism.L2.DIV.lvlIdem_idem]
    obtain ⟨r, hr, hle⟩ := GlobalTheory.T.finrank_range_idempotent_le_of_embedsInRegular ℂ Γ V ρ (H k) (n k) (hemb k) (b k * p) (hsupp k) hid
    rw [hcoeff k] at hr
    have hHb : (0 : ℝ) < Nat.card Hb := by exact_mod_cast Nat.card_pos
    have hH : (0 : ℝ) < Nat.card (H k) := by exact_mod_cast Nat.card_pos
    have hrR : (r : ℝ) * Nat.card Hb = Nat.card (H k) * s k := by
      have hHbC : (Nat.card Hb : ℂ) ≠ 0 := by exact_mod_cast hHb.ne'
      have : ((r : ℝ) * Nat.card Hb : ℝ) = ((Nat.card (H k) * s k : ℝ) : ℂ) := by
        push_cast; rw [hr]; field_simp
      exact_mod_cast this
    have hs : 0 ≤ s k := by
      have : 0 ≤ (Nat.card (H k) : ℝ) * s k := by rw [← hrR]; positivity
      exact le_of_mul_le_mul_left (by simpa using this) hH
    have hd : (0 : ℝ) ≤ finrank ℂ (eig ρ Hb lam) := by positivity
    have hleR : (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤ n k * r := by exact_mod_cast hle
    have key : ((n k : ℝ) * r) * Nat.card Hb ≤ (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb := by
      calc ((n k : ℝ) * r) * Nat.card Hb = ((n k : ℝ) * Nat.card (H k)) * s k := by rw [mul_assoc, hrR]; ring
        _ ≤ (c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) * s k := mul_le_mul_of_nonneg_right (hcard k) hs
        _ = (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb := by ring
    exact hleR.trans (le_of_mul_le_mul_right key hHb)
  have hdimR : (finrank ℂ W : ℝ) ≤ (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 0 * p))) : ℝ) +
      finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 1 * p))) := by exact_mod_cast hdim
  calc (finrank ℂ W : ℝ) ≤ _ := hdimR
    _ ≤ c * s 0 * finrank ℂ (eig ρ Hb lam) + c * s 1 * finrank ℂ (eig ρ Hb lam) := add_le_add (hbnd 0) (hbnd 1)
    _ = c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by ring

end GlobalTheory.BadCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHens
section
open IsLocalRing GlobalTheory.Henselisation

noncomputable section

namespace GlobalTheory.Henselisation

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem Hens.of_trans {i j : EtNbhd R} (h : i ≤ j) (y : i.B) :
    Hens.of j (EtNbhd.trans h y) = Hens.of i y :=
  Ring.DirectLimit.of_f h y

theorem Hens.exists_of (hdir : IsDirected (EtNbhd R) (· ≤ ·)) (z : Hens R) :
    ∃ (i : EtNbhd R) (y : i.B), Hens.of i y = z :=
  haveI : IsDirectedOrder (EtNbhd R) := hdir
  Ring.DirectLimit.exists_of (G := fun i : EtNbhd R => i.B)
    (f := fun _ _ h => ⇑(EtNbhd.trans h)) z

theorem Hens.exists_of_fin (hdir : IsDirected (EtNbhd R) (· ≤ ·)) :
    ∀ (l : ℕ) (x : Fin l → Hens R), ∃ (i : EtNbhd R) (y : Fin l → i.B), ∀ k, Hens.of i (y k) = x k := by
  intro l
  induction l with
  | zero => exact fun x => ⟨EtNbhd.base, fun k => k.elim0, fun k => k.elim0⟩
  | succ l ih =>
    intro x
    obtain ⟨i, y, hy⟩ := ih (fun k => x k.castSucc)
    obtain ⟨j, z, hz⟩ := Hens.exists_of hdir (x (Fin.last l))
    obtain ⟨m, him, hjm⟩ := directed_of (· ≤ ·) i j
    refine ⟨m, Fin.lastCases (EtNbhd.trans hjm z) (fun k => EtNbhd.trans him (y k)), ?_⟩
    intro k
    induction k using Fin.lastCases with
    | last => dsimp only; rw [Fin.lastCases_last, Hens.of_trans, hz]
    | cast k => dsimp only; rw [Fin.lastCases_castSucc, Hens.of_trans, hy]

theorem flat_hens_of_stages (hdir : IsDirected (EtNbhd R) (· ≤ ·))
    (hinj : ∀ i : EtNbhd R, Function.Injective (Hens.of i))
    (halg : ∀ (i : EtNbhd R) (r : R), Hens.of i (algebraMap R i.B r) = algebraMap R (Hens R) r)
    (hflat : ∀ i : EtNbhd R, Module.Flat R i.B) : Module.Flat R (Hens R) := by
  have hsmul : ∀ (i : EtNbhd R) (r : R) (y : i.B), Hens.of i (r • y) = r • Hens.of i y := by
    intro i r y
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halg]
  refine Module.Flat.iff_forall_isTrivialRelation.mpr ?_
  intro l f x hfx
  obtain ⟨i, y, hy⟩ := Hens.exists_of_fin hdir l x
  have h0 : ∑ k, f k • y k = 0 := by
    apply hinj i
    rw [map_zero, map_sum]
    simp only [hsmul, hy]
    exact hfx
  obtain ⟨k, a, z, hya, haf⟩ := Module.Flat.iff_forall_isTrivialRelation.mp (hflat i) h0
  refine ⟨k, a, fun j => Hens.of i (z j), fun m => ?_, haf⟩
  rw [← hy m, hya m, map_sum]
  simp only [hsmul]

theorem flat_hens : ∀ (R : Type) [CommRing R] [IsLocalRing R], Module.Flat R (Hens R) :=
  fun R _ _ => flat_hens_of_stages (GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd R) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R) (GlobalTheory.T.flat_localRing_pointedEtaleNeighbourhood R)

end GlobalTheory.Henselisation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinors
section
open Classical MvPolynomial

noncomputable section

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

theorem eval_rsub_frameMat {a d : ℕ} (x₀ : Var ι d a → ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) (rsub (frameMat x₀) P) = eval x₀ (colSub g P) := by
  have h : (eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2)).comp
        (rsub (frameMat x₀) : Pol ι d a →ₐ[ℂ] _).toRingHom
      = (eval x₀).comp (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro v
      obtain ⟨τ, r, j⟩ := v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rsub_X, colSub, aeval_X,
        map_sum, map_mul, eval_C, eval_X]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single j]
        · simp [frameMat, mul_comm]
        · intro b _ hb; simp [frameMat, hb]
        · simp
      · intro b _ hb; simp [frameMat, hb]
      · simp
  exact congrArg (fun φ : Pol ι d a →+* ℂ => φ P) h

theorem rsub_frameMat_of_mem_inv {a d : ℕ} {n : ι → ℕ} (x₀ : Var ι d a → ℂ) {P : Pol ι d a}
    (hP : P ∈ inv a d n) : rsub (frameMat x₀) P = eval x₀ P • detG a n := by
  rw [← sub_eq_zero]
  apply GlobalTheory.T.unitaryGroup_family_zariski_dense
  intro g
  rw [map_sub, eval_rsub_frameMat x₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P, hP g, smul_eval, smul_eval,
    eval_detG a n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))]
  ring

theorem inv_le_span_prodMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by
  intro ι _ a d n P hP
  set c := Formalism.L2.DIV.fockS (detG (ι := ι) a n) (detG a n) with hc
  have hc0 : c ≠ 0 := fun h => by
    have := fockS_self_re_pos (detG_ne_zero (ι := ι) a n)
    rw [← hc, h] at this
    simp at this
  have key : c • P = ∑ T : Tup ι a d n, Formalism.L2.DIV.fockS (prodMinors T) P • prodMinors T := by
    apply MvPolynomial.funext
    intro x₀
    have h1 := GlobalTheory.T.fockPairing_linearSubstitution_adjoint (frameMat x₀).conjTranspose (detG a n) P
    rw [Matrix.conjTranspose_conjTranspose, rsub_frameMat_of_mem_inv x₀ hP, GlobalTheory.T.cauchyBinet_columnFrame_prodDetPow_eq_sum] at h1
    rw [← Formalism.L2.DIV.fockL_apply, ← Formalism.L2.DIV.fockL_apply, map_sum, map_smul, LinearMap.sum_apply] at h1
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, Formalism.L2.DIV.fockL_apply, smul_eq_mul,
      starRingEnd_apply, star_star] at h1
    rw [smul_eval, map_sum]
    simp only [smul_eval]
    rw [mul_comm, ← h1]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  have hP' : P = c⁻¹ • ∑ T : Tup ι a d n, Formalism.L2.DIV.fockS (prodMinors T) P • prodMinors T := by
    rw [← key, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hP']
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun T _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩))

end GlobalTheory.MinorFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.EndLoc.ActUnr

section Chart

variable {X Y₁ Y₂ Z W : Scheme.{0}}

def chartPullPullAlong (L : LB X) (a₁ : Y₁ ⟶ X) (a₂ : Z ⟶ Y₁) (c₁ : Y₂ ⟶ X) (c₂ : W ⟶ Y₂) (h : Z ⟶ W)
    (e : a₂ ≫ a₁ = h ≫ c₂ ≫ c₁) : ChartPull ((L.pull a₁).pull a₂) ((L.pull c₁).pull c₂) h where
  idx J := fun _ _ => J PUnit.unit PUnit.unit
  le J y hy := by
    have h₁ := mem_pull.1 (mem_pull.1 hy)
    have h₂ : (a₂ ≫ a₁) y ∈ L.U (J PUnit.unit PUnit.unit) := by simpa using h₁
    rw [e] at h₂
    exact mem_pull.2 (mem_pull.2 (by simpa using h₂))
  g y J J' hj hj' := by
    have hc : ∀ K : PUnit → PUnit → L.ι, y ∈ ((L.pull a₁).pull a₂).U K →
        h y ∈ ((L.pull c₁).pull c₂).U (fun _ _ => K PUnit.unit PUnit.unit) := fun K hK => by
      have h₁ := mem_pull.1 (mem_pull.1 hK)
      have h₂ : (a₂ ≫ a₁) y ∈ L.U (K PUnit.unit PUnit.unit) := by simpa using h₁
      rw [e] at h₂
      exact mem_pull.2 (mem_pull.2 (by simpa using h₂))
    have l₁ := gm_pull_g (L.pull a₁) a₂ (𝟙 Z) y J J' hj hj'
    rw [Category.id_comp] at l₁
    have l₂ := gm_pull_g L a₁ a₂ y (J PUnit.unit) (J' PUnit.unit) (mem_pull.1 hj) (mem_pull.1 hj')
    have l₃ := gm_pull_g (L.pull c₁) c₂ h y (fun _ _ => J PUnit.unit PUnit.unit)
      (fun _ _ => J' PUnit.unit PUnit.unit) (hc J hj) (hc J' hj')
    have l₄ := gm_pull_g L c₁ (h ≫ c₂) y (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
      (mem_pull.1 (hc J hj)) (mem_pull.1 (hc J' hj'))
    rw [l₁, l₂, l₃, l₄, e, Category.assoc]

theorem lbIso_pullPull_along (Q : LB X) (φ₂ : Y₁ ⟶ X) (m₁ m₂ : Y₁ ⟶ Y₁) (φ₂' : Y₂ ⟶ X) (m₁' m₂' : Y₂ ⟶ Y₂)
    (u : Y₂ ⟶ Y₁) (hφ : φ₂' = u ≫ φ₂) (h₁ : m₁' ≫ u = u ≫ m₁) (h₂ : m₂' ≫ u = u ≫ m₂)
    (H : LBIso ((Q.pull φ₂).pull m₁) ((Q.pull φ₂).pull m₂)) :
    LBIso ((Q.pull φ₂').pull m₁') ((Q.pull φ₂').pull m₂') :=
  LBIso.chartPull
    (chartPullPullAlong Q φ₂' m₁' φ₂ m₁ u (by rw [hφ, ← Category.assoc, h₁, Category.assoc]))
    (chartPullPullAlong Q φ₂' m₂' φ₂ m₂ u (by rw [hφ, ← Category.assoc, h₂, Category.assoc])) H

end Chart

section Square

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {B : Over S'} {φ : B.left ⟶ G.left}

def sqMap (w : φ ≫ G.hom = B.hom ≫ f) : (B ⊗ B).left ⟶ (G ⊗ G).left :=
  (lift (pushPt w (fst B B)) (pushPt w (snd B B))).left

theorem sqMap_fst (w : φ ≫ G.hom = B.hom ≫ f) : sqMap w ≫ (fst G G).left = (fst B B).left ≫ φ :=
  congrArg (fun z => z.left) (lift_fst (pushPt w (fst B B)) (pushPt w (snd B B)))

theorem sqMap_snd (w : φ ≫ G.hom = B.hom ≫ f) : sqMap w ≫ (snd G G).left = (snd B B).left ≫ φ :=
  congrArg (fun z => z.left) (lift_snd (pushPt w (fst B B)) (pushPt w (snd B B)))

theorem left_hom_ext {H Z : Scheme.{0}} {G : Over H} {x y : Z ⟶ (G ⊗ G).left}
    (h1 : x ≫ (fst G G).left = y ≫ (fst G G).left) (h2 : x ≫ (snd G G).left = y ≫ (snd G G).left) : x = y := by
  have hw : y ≫ (G ⊗ G).hom = x ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, ← h1, Category.assoc]
  let x' : Over.mk (x ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk x rfl
  let y' : Over.mk (x ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk y hw
  have : x' = y' := CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext h1) (Over.OverMorphism.ext h2)
  exact congrArg (fun t => t.left) this

theorem lift_left_comp_sqMap (w : φ ≫ G.hom = B.hom ≫ f) (x' y' : B ⊗ B ⟶ B) (x y : G ⊗ G ⟶ G)
    (hx : x'.left ≫ φ = sqMap w ≫ x.left) (hy : y'.left ≫ φ = sqMap w ≫ y.left) :
    (lift x' y').left ≫ sqMap w = sqMap w ≫ (lift x y).left := by
  apply left_hom_ext
  · rw [Category.assoc, sqMap_fst, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc,
      ← Over.comp_left, lift_fst]
  · rw [Category.assoc, sqMap_snd, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc,
      ← Over.comp_left, lift_snd]

end Square

section Act

variable {O : Type} [Ring O]

theorem isRAct_pullback {H T : Scheme.{0}} (g : T ⟶ H) (AH : Over H) [GrpObj AH] (act : O → (AH ⟶ AH))
    (h : IsRAct AH act) : IsRAct ((Over.pullback g).obj AH) (fun a => (Over.pullback g).map (act a)) := by
  refine ⟨fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩
  · haveI := h.1 a
    infer_instance
  · dsimp only
    rw [h.2.1]
    exact (Over.pullback g).map_id _
  · dsimp only
    rw [h.2.2.1, Functor.map_comp]
  · dsimp only
    rw [h.2.2.2, Functor.map_mul]

theorem isRAct_conj {T : Scheme.{0}} {B C : Over T} [GrpObj B] [GrpObj C] (e : B ≅ C) [IsMonHom e.hom]
    (act : O → (C ⟶ C)) (h : IsRAct C act) : IsRAct B (fun a => e.hom ≫ act a ≫ e.inv) := by
  refine ⟨fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩
  · haveI := h.1 a
    infer_instance
  · simp only [h.2.1, Category.id_comp, Iso.hom_inv_id]
  · simp only [h.2.2.1, Category.assoc, Iso.inv_hom_id_assoc]
  · dsimp only
    rw [h.2.2.2, MonObj.mul_comp, MonObj.comp_mul]

theorem adj_along {H T : Scheme.{0}} {AH : Over H} {AT : Over T} [GrpObj AH] [GrpObj AT] {g : T ⟶ H}
    {χ : AT.left ⟶ AH.left} (w : χ ≫ AH.hom = AT.hom ≫ g) (act : O → (AH ⟶ AH)) (v : O → (AT ⟶ AT))
    (hv : ∀ a, (v a).left ≫ χ = χ ≫ (act a).left) {X : Scheme.{0}} (Q : LB X) (φ₂ : (AH ⊗ AH).left ⟶ X)
    (bar : O → O) (h : Adj AH (Q.pull φ₂) bar act) : Adj AT (Q.pull (sqMap w ≫ φ₂)) bar v := fun a =>
  lbIso_pullPull_along Q φ₂ _ _ (sqMap w ≫ φ₂) _ _ (sqMap w) rfl
    (lift_left_comp_sqMap w _ _ _ _
      (by rw [Over.comp_left, Category.assoc, hv, ← Category.assoc, ← sqMap_fst w, Category.assoc, Over.comp_left])
      (by rw [sqMap_snd]))
    (lift_left_comp_sqMap w _ _ _ _ (by rw [sqMap_fst])
      (by rw [Over.comp_left, Category.assoc, hv, ← Category.assoc, ← sqMap_snd w, Category.assoc, Over.comp_left]))
    (h a)

end Act

end GlobalTheory.EndLoc.ActUnr

namespace GlobalTheory.EndLoc

open ActUnr in

theorem formallyUnramified_actRep : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left)
    (O : Type) [Ring O] (bar : O → O) (R : ActRep A Q bar), IsAbelianScheme A → FormallyUnramified R.π := by
  intro S A _ _ Q O _ bar Rp hA
  refine FormallyUnramified.of_hom_ext _ fun R R₀ q hq hsq g₁ g₂ hi hg ↦ ?_
  let f : Spec R ⟶ S := g₁ ≫ Rp.π
  let AT : Over (Spec R) := (Over.pullback f).obj A
  let ψ : AT.left ⟶ A.left := pullback.fst A.hom f
  have hAT : IsGrpPullback AT A f ψ := isGrpPullback_pullback A f
  have hAbT : IsAbelianScheme AT := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have build : ∀ g : Spec R ⟶ Rp.H, g ≫ Rp.π = f → ∃ (v : O → (AT ⟶ AT)) (χ : AT.left ⟶ Rp.AH.left)
      (φ₂' : (AT ⊗ AT).left ⟶ (A ⊗ A).left),
      IsRAct AT v ∧ IsSquare ψ φ₂' ∧ Adj AT (Q.pull φ₂') bar v ∧ IsGrpPullback AT Rp.AH g χ ∧ χ ≫ Rp.φ = ψ ∧
        ∀ a, (v a).left ≫ χ = χ ≫ (Rp.act a).left := by
    intro g hgf
    have h' : IsGrpPullback ((Over.pullback g).obj Rp.AH) A f (pullback.fst Rp.AH.hom g ≫ Rp.φ) :=
      ((isGrpPullback_pullback Rp.AH g).comp Rp.pb).congr hgf rfl
    obtain ⟨e, he, heφ⟩ := grpPullback_iso hAT h'
    haveI := he
    have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
    let χ : AT.left ⟶ Rp.AH.left := e.hom.left ≫ pullback.fst Rp.AH.hom g
    let v : O → (AT ⟶ AT) := fun a ↦ e.hom ≫ (Over.pullback g).map (Rp.act a) ≫ e.inv
    have hχφ : χ ≫ Rp.φ = ψ := by simp only [χ, Category.assoc]; exact heφ
    have hw : χ ≫ Rp.AH.hom = AT.hom ≫ g := by
      simp only [χ]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      congr 1
      exact Over.w e.hom
    have hv : ∀ a, (v a).left ≫ χ = χ ≫ (Rp.act a).left := fun a ↦ by
      have hm : ((Over.pullback g).map (Rp.act a)).left ≫ pullback.fst Rp.AH.hom g =
          pullback.fst Rp.AH.hom g ≫ (Rp.act a).left := pullback.lift_fst _ _ _
      simp only [v, χ, Over.comp_left, Category.assoc]
      rw [reassoc_of% hie, hm]
    have hR : IsRAct AT v := isRAct_conj e _ (isRAct_pullback g Rp.AH Rp.act Rp.isAct)
    refine ⟨v, χ, sqMap hw ≫ Rp.φ₂, hR, ⟨?_, ?_⟩, adj_along hw Rp.act v hv Q Rp.φ₂ bar Rp.adj,
      Rp.pb.cancel ((hAT.congr hgf.symm hχφ.symm)) hw, hχφ, hv⟩
    · rw [Category.assoc, Rp.sq.1, ← Category.assoc, sqMap_fst, Category.assoc, hχφ]
    · rw [Category.assoc, Rp.sq.2, ← Category.assoc, sqMap_snd, Category.assoc, hχφ]
  obtain ⟨v₁, χ₁, φ₂₁, hR₁, hsq₁, hadj₁, hpb₁, hχ₁φ, hχ₁u⟩ := build g₁ rfl
  obtain ⟨v₂, χ₂, -, hR₂, -, -, hpb₂, hχ₂φ, hχ₂u⟩ := build g₂ hg.symm
  let I : Ideal R := RingHom.ker q.hom
  have hI : IsNilpotent I := ⟨2, hsq⟩
  let j : Sp (R ⧸ I) ⟶ Sp R := spMap (Ideal.Quotient.mk I)
  have hj : j ≫ g₁ = j ≫ g₂ := by
    let ε : (R ⧸ I) ≃+* R₀ := RingHom.quotientKerEquivOfSurjective hq
    have hε : Spec.map q = Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ j := by
      rw [← Spec.map_comp]
      congr 1
    haveI : IsIso (CommRingCat.ofHom ε.toRingHom) := ε.toCommRingCatIso.isIso_hom
    rw [hε, Category.assoc, Category.assoc] at hi
    exact (cancel_epi _).1 hi
  have hχ : pullback.fst AT.hom j ≫ χ₁ = pullback.fst AT.hom j ≫ χ₂ := by
    apply Rp.pb.1.hom_ext
    · rw [Category.assoc, Category.assoc, hχ₁φ, hχ₂φ]
    · rw [Category.assoc, Category.assoc, hpb₁.1.w, hpb₂.1.w, pullback.condition_assoc, pullback.condition_assoc, hj]
  have hv : ∀ a, v₁ a = v₂ a := fun a ↦ by
    haveI := hR₁.1 a
    haveI := hR₂.1 a
    refine GlobalTheory.NilRigidity.eq_of_pullback_quotient_eq I hI AT AT hAbT (v₁ a) (v₂ a) ?_
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [show ((Over.pullback j).map (v₁ a)).left ≫ pullback.fst AT.hom j =
          pullback.fst AT.hom j ≫ (v₁ a).left from pullback.lift_fst _ _ _,
        show ((Over.pullback j).map (v₂ a)).left ≫ pullback.fst AT.hom j =
          pullback.fst AT.hom j ≫ (v₂ a).left from pullback.lift_fst _ _ _]
      apply hAT.1.hom_ext
      · calc (pullback.fst AT.hom j ≫ (v₁ a).left) ≫ ψ
            = pullback.fst AT.hom j ≫ (v₁ a).left ≫ χ₁ ≫ Rp.φ := by rw [hχ₁φ, Category.assoc]
          _ = pullback.fst AT.hom j ≫ χ₁ ≫ (Rp.act a).left ≫ Rp.φ := by rw [reassoc_of% (hχ₁u a)]
          _ = pullback.fst AT.hom j ≫ χ₂ ≫ (Rp.act a).left ≫ Rp.φ := by rw [reassoc_of% hχ]
          _ = pullback.fst AT.hom j ≫ (v₂ a).left ≫ χ₂ ≫ Rp.φ := by rw [reassoc_of% (hχ₂u a)]
          _ = (pullback.fst AT.hom j ≫ (v₂ a).left) ≫ ψ := by rw [hχ₂φ, Category.assoc]
      · rw [Category.assoc, Category.assoc, Over.w (v₁ a), Over.w (v₂ a)]
    · rw [show ((Over.pullback j).map (v₁ a)).left ≫ pullback.snd AT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _,
        show ((Over.pullback j).map (v₂ a)).left ≫ pullback.snd AT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _]
  obtain ⟨g, -, hg'⟩ := Rp.rep (Spec R) f AT ψ φ₂₁ v₁ hAT hsq₁ hR₁ hadj₁
  have e1 := hg' g₁ ⟨rfl, χ₁, hpb₁, hχ₁φ, hχ₁u⟩
  have e2 := hg' g₂ ⟨hg.symm, χ₂, hpb₂, hχ₂φ, fun a ↦ by rw [hv a]; exact hχ₂u a⟩
  rw [e1, e2]

end GlobalTheory.EndLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstant
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem frame_coord : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    CohomZeroIsConstants F → ∀ (n : ℕ) (Φ : Frame F n), ∃ l : Fin n → (Glob1 F →ₗ[R] R),
      (∀ i (w : Glob1 F) T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (l i w)) ∧
        ∀ w, w = ∑ i, l i w • Φ.w i := by
  intro R _ C _ F hF n Φ
  have hd : ∀ i (w : Glob1 F), d0 F (fun T ↦ Φ.δ i T (w.1 T)) = 0 := by
    intro i w
    funext T T' φ
    rw [amitsur_d0_apply, w.2 φ, Φ.nat]
    exact sub_self _
  let c : Fin n → Glob1 F → R := fun i w ↦ (hF _ (hd i w)).exists.choose
  have hc : ∀ i w T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (c i w) :=
    fun i w ↦ (hF _ (hd i w)).exists.choose_spec
  have uniq : ∀ i w (r : R), (∀ T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) r) → c i w = r :=
    fun i w r hr ↦ (hF _ (hd i w)).unique (hc i w) hr
  refine ⟨fun i ↦
    { toFun := c i
      map_add' := fun w w' ↦ uniq i (w + w') _ (fun T ↦ by
        rw [Submodule.coe_add, Pi.add_apply, map_add, hc, hc, map_add])
      map_smul' := fun r w ↦ uniq i (r • w) _ (fun T ↦ by
        rw [Submodule.coe_smul, Pi.smul_apply, ← algebraMap_smul (F.obj T) r (w.1 T), map_smul, hc,
          RingHom.id_apply, smul_eq_mul, smul_eq_mul, map_mul]) },
    fun i w T ↦ hc i w T, fun w ↦ ?_⟩
  apply Subtype.ext
  funext T
  rw [Submodule.coe_sum, Finset.sum_apply]
  conv_lhs => rw [Φ.sum T (w.1 T)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hc, Submodule.coe_smul, Pi.smul_apply, algebraMap_smul]
  rfl

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTnScalarUniformiserSingleTranslationStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTn_scalar_uniformiser_single_translation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w n), ∃ g, GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n) x = ρ g x := by
  first | exact @GlobalTheory.LFun.tn_single | exact GlobalTheory.LFun.tn_single | (intros; apply GlobalTheory.LFun.tn_single <;> assumption)
end

