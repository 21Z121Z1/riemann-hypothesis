import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0004
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceLatDualIiiOf
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev fI (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)

theorem pairA_mul_one (α : Af D.host.F) : pairA D.host.F 0 α * pairA D.host.F 0 1 = pairA D.host.F 0 α :=
  Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [mul_zero]) (by show α * 1 = α; rw [mul_one])

theorem splitIdem_mul_fI {e' : AE D} (h : IsSplitIdem D e') : e' * fI D = e' := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -, -⟩, h3⟩ := h
  have he : e' = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) := by
    rw [← h3, mul_add, h1, h2, add_zero]
  calc e' * fI D = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * fI D := by rw [← he]
    _ = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α * pairA D.host.F 0 1) := by
        rw [map_mul, mul_assoc]
    _ = e' := by rw [pairA_mul_one, ← he]

theorem splitIdem_cA {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hv, by rw [cA_cA, add_comm, h3]⟩

theorem idemSum_mul_fI {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) :
    e * fI D = e ∧ cA D e * fI D = cA D e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_mul, map_sum, Finset.sum_mul]
  exact ⟨Finset.sum_congr rfl fun PP hPP => splitIdem_mul_fI (hes PP hPP).1,
    Finset.sum_congr rfl fun PP hPP => splitIdem_mul_fI (splitIdem_cA (hes PP hPP).1)⟩

theorem idemSum_int {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) :
    finPart D e ∈ intAE D ∧ finPart D (cA D e) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  refine ⟨?_, ?_⟩
  · rw [map_sum]
    exact AddSubgroup.sum_mem _ fun PP hPP => splitIdem_int (hes PP hPP).1
  · rw [map_sum, map_sum]
    exact AddSubgroup.sum_mem _ fun PP hPP => splitIdem_int (splitIdem_cA (hes PP hPP).1)

theorem infPart_fI : infPart D (fI D) = 0 := by
  show infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)) = 0
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
    (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show fstA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 0
  rw [show fstA D.host.F (pairA D.host.F 0 1) = 0 from rfl, TensorProduct.zero_tmul]

theorem half_infPart {m n : ℕ} {f : AE D} (hf : f * fI D = f) {y : Mx D m n} (hy : IsHalf f y) :
    y.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  calc infPart D (y i j) = infPart D ((f * fI D) * y i j) := by rw [hf, hy i j]
    _ = 0 := by rw [map_mul, map_mul, infPart_fI, mul_zero, zero_mul]

variable (S T : HSp D)

theorem hO_half_right {f : AE D} {y : WO S T} (hy : IsHalf (cA D f) y) (u : WO S T) :
    hO S T y u = hO S T y (f • u) := by
  unfold hO
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  conv_lhs => rw [← hy d a]
  ring

theorem symplO_half_right {f : AE D} {y : WO S T} (hy : IsHalf (cA D f) y) (u : WO S T) :
    symplO S T y u = symplO S T y (f • u) := by
  unfold symplO; rw [hO_half_right S T hy u]

variable {S T}

theorem placeLatDualIi_of (hL : LatSelfDual D) : PlaceLatDualIi D := by
  intro ψ hψ S T ΛS ΛT hS hT P e he y hy
  have hL4 := (hL ψ hψ S T ΛS ΛT hS hT).2.2.2
  obtain ⟨hfe, hfc⟩ := idemSum_mul_fI he
  have hie := (idemSum_int he).1
  have hee := idemSum_mul_self he
  have hy0 : y.map (infPart D) = 0 := half_infPart hfc hy
  constructor
  · intro hx
    refine (hL4 y hy0).2 fun u hu => ?_
    have hm : e • u ∈ latAll S T ΛS ΛT := latO_smul_mem S T ΛS ΛT hie hu
    have hh : IsHalf e (e • u) := fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
    have h1 := hx _ hm hh
    rw [symplO_half_right S T hy u, symplO_swap S T (e • u) y, AddChar.map_neg_eq_inv, h1, inv_one]
  · intro hyL x hx hxh
    exact (hL4 x (half_infPart hfe hxh)).1 hx y hyL

theorem placeLatDualIii_of (hL : LatSelfDual D) : PlaceLatDualIii D := by
  intro ψ hψ S T ΛS ΛT hS hT P e he x hx
  have hL4 := (hL ψ hψ S T ΛS ΛT hS hT).2.2.2
  obtain ⟨hfe, -⟩ := idemSum_mul_fI he
  have hic := (idemSum_int he).2
  have hee := idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hx0 : x.map (infPart D) = 0 := half_infPart hfe hx
  have hxc : IsHalf (cA D (cA D e)) x := by rw [cA_cA]; exact hx
  constructor
  · intro hy
    refine (hL4 x hx0).2 fun u hu => ?_
    have hm : cA D e • u ∈ latAll S T ΛS ΛT := latO_smul_mem S T ΛS ΛT hic hu
    have hh : IsHalf (cA D e) (cA D e • u) := fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hcc]
    rw [symplO_half_right S T hxc u]
    exact hy _ hm hh
  · intro hxL y hy _
    exact (hL4 x hx0).1 hxL y hy

end Formalism.IndefR.Fin.PDA

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitChar
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField Formalism.IndefR.DeterminantProjection Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin

namespace SplitChar

theorem exists_place_two (F : Type) [Field F] [NumberField F] :
    ∃ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal := by
  have h2 : ¬ IsUnit (2 : 𝓞 F) := by
    intro hu
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [show (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 by simp, Algebra.norm_algebraMap] at hn
    have hr : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    have hge : (2 : ℤ) ≤ 2 ^ Module.finrank ℤ (𝓞 F) := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Module.finrank ℤ (𝓞 F) := pow_le_pow_right₀ (by norm_num) hr
    rcases Int.isUnit_iff.mp hn with h | h <;> omega
  obtain ⟨M, hM, h2M⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have h2mem : (2 : 𝓞 F) ∈ M := h2M (Ideal.mem_span_singleton_self 2)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    have h0 : (2 : 𝓞 F) = 0 := (Submodule.mem_bot _).mp h2mem
    have h0' : (2 : F) = 0 := by
      have := congrArg (algebraMap (𝓞 F) F) h0
      rwa [map_ofNat, map_zero] at this
    exact two_ne_zero h0'
  exact ⟨⟨M, hM.isPrime, hM0⟩, h2mem⟩

theorem exists_splitIdem_D (D : D7) : ∃ e, IsSplitIdem D e := by
  obtain ⟨v, hv⟩ := exists_place_two D.host.F
  obtain ⟨e, ε, he, -, -⟩ := twoSplitIdem D v hv
  exact ⟨e, he⟩

variable {D : D7}

theorem ga_ext (V : HSp D) {g g' : GA D V} (h : mt V g = mt V g') : g = g' :=
  Subtype.ext (Units.ext h)

def RA (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E) :
    Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
  proj (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv)

theorem haA (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) :
    incA D ainv * hsq (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) = 1 := by
  rw [← hsq_map (incA D) (flipTwoThree.sigE D) (cA D) (fun a => (flipTwoThree.cA_incA' a).symm), ← map_mul, ha, map_one]

theorem hainvA (ainv : D.host.E) (hainv : flipTwoThree.sigE D ainv = ainv) : cA D (incA D ainv) = incA D ainv := by
  rw [flipTwoThree.cA_incA', hainv]

theorem RA_idem (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) : RA V u ainv * RA V u ainv = RA V u ainv :=
  proj_idem' _ _ _ _ (haA V u ainv ha)

theorem mul_aux {n : Type} [Fintype n] [DecidableEq n] (R : Matrix n n (AE D)) (hRR : R * R = R)
    (a b : AE D) : (1 + (a - 1) • R) * (1 + (b - 1) • R) = 1 + (a * b - 1) • R := by
  simp only [add_mul, mul_add, one_mul, mul_one]
  rw [smul_mul_smul_comm, hRR, show a * b - 1 = (b - 1) + ((a - 1) + (a - 1) * (b - 1)) by ring, add_smul,
    add_smul]
  abel

def secM (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E) (x : AE D) :
    Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
  1 + (x - 1) • RA V u ainv

theorem secM_unitary (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (hainv : flipTwoThree.sigE D ainv = ainv) (x : AE D)
    (hx : cA D x * x = 1) :
    ((secM V u ainv x).map (cA D))ᵀ * V.gram.map (incA D) * secM V u ainv x = V.gram.map (incA D) :=
  proj_unitary (cA D) Formalism.L2.Theta.cA_cA (V.gram.map (incA D)) (flipTwoThree.gramA_herm V) _ _ (haA V u ainv ha)
    (hainvA ainv hainv) x hx

theorem secM_det (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (x : AE D) : (secM V u ainv x).det = x :=
  det_proj' (cA D) _ _ _ (haA V u ainv ha) x

theorem unitary_one_conj_mul_self (x : FirstPropositionFrame D) : cA D (((x : (AE D)ˣ)) : AE D) * (((x : (AE D)ˣ)) : AE D) = 1 := by
  rw [mul_comm]; exact x.2

def secG (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (hainv : flipTwoThree.sigE D ainv = ainv) (x : FirstPropositionFrame D) : GA D V :=
  flipTwoThree.mkGA V (secM V u ainv ((x : (AE D)ˣ) : AE D)) (secM_unitary V u ainv ha hainv _ (unitary_one_conj_mul_self x))
    (by rw [secM_det V u ainv ha]; exact (x : (AE D)ˣ).isUnit)

theorem mt_secG (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (hainv : flipTwoThree.sigE D ainv = ainv) (x : FirstPropositionFrame D) :
    mt V (secG V u ainv ha hainv x) = secM V u ainv ((x : (AE D)ˣ) : AE D) := rfl

def secHom (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (hainv : flipTwoThree.sigE D ainv = ainv) : FirstPropositionFrame D →* GA D V where
  toFun := secG V u ainv ha hainv
  map_one' := by
    apply ga_ext V
    rw [mt_secG, flipTwoThree.mt_one']
    simp [secM]
  map_mul' x y := by
    apply ga_ext V
    rw [flipTwoThree.mt_mul', mt_secG, mt_secG, mt_secG]
    simp only [secM, Subgroup.coe_mul, Units.val_mul]
    exact (mul_aux _ (RA_idem V u ainv ha) _ _).symm

end SplitChar

end Formalism.IndefR.Fin

end
end

