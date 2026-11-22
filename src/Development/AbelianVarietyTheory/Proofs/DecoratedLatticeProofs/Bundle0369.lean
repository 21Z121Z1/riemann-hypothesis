import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeAtPlacesCongrLocalLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.FinPl.LatCong

open GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem latV_mono' (V : HSp D) (L : Lat V) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) :
    latV V L P ≤ latV V L P' := by
  apply AddSubgroup.closure_mono
  rintro y ⟨α, hα, h0, r⟩
  exact ⟨α, hα, fun v hv => h0 v fun h' => hv (h v h'), r⟩

theorem latO_le_right (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (N' M' : Lat T) (P : Pl D → Prop)
    (h : latV T N' P ≤ latV T M' P) :
    latO S T LS (N' : Set _) P ≤ latO S T LS (M' : Set _) P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  let c : Fin S.rank → AE D := fun j => (1 : AF D.host.F) ⊗ₜ[D.host.F] (a * ∑ k, star (s k) * S.gram k j)
  let Φ : (Fin T.rank → AE D) →+ WO S T :=
    AddMonoidHom.mk' (fun u => Matrix.of fun i j => u i * c j) (by
      intro u u'; ext i j; simp [add_mul])
  have key : latV T M' P ≤ (latO S T LS (M' : Set _) P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, hγP, b, hb, m, hm, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine AddSubgroup.subset_closure ⟨γ, hγ, hγP, a, ha, s, hs, m, hm, ?_⟩
    ext i j
    simp only [Φ, c, AddMonoidHom.mk'_apply, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    ring
  have hmem : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * t i)) ∈ latV T N' P :=
    AddSubgroup.subset_closure ⟨α, hα, hP, 1, rfl, t, ht, rfl⟩
  have e : Φ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * t i)) =
      Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) := by
    ext i j
    simp only [Φ, c, AddMonoidHom.mk'_apply, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    ring
  have h2 := AddSubgroup.mem_comap.1 (key (h hmem))
  rw [e] at h2
  exact h2

theorem latO_le_left (S T : HSp D) (N M : Lat S) (LT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop)
    (h : latV S N P ≤ latV S M P) :
    latO S T (N : Set _) LT P ≤ latO S T (M : Set _) LT P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  let Φ : (Fin S.rank → AE D) →+ WO S T :=
    AddMonoidHom.mk' (fun y => Matrix.of fun i j => ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * t i)) *
      ∑ k, cA D (y k) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram k j)) (by
      intro u u'; ext i j; simp [map_add, add_mul, Finset.sum_add_distrib, mul_add])
  have gen : ∀ (γ : Af D.host.F) (x : Fin S.rank → D.host.E),
      Φ (fun k => pairA D.host.F 0 γ ⊗ₜ[D.host.F] (1 * x k)) =
        Matrix.of fun i j => pairA D.host.F 0 γ ⊗ₜ[D.host.F] (a * t i * ∑ k, star (x k) * S.gram k j) := by
    intro γ x
    ext i j
    simp only [Φ, AddMonoidHom.mk'_apply, Matrix.of_apply, one_mul]
    change (1 ⊗ₜ[D.host.F] (a * t i)) * ∑ k, (pairA D.host.F 0 γ ⊗ₜ[D.host.F] star (x k)) * (1 ⊗ₜ[D.host.F] S.gram k j) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Finset.mul_sum, one_mul, ← TensorProduct.tmul_sum]
  have key : latV S M P ≤ (latO S T (M : Set _) LT P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, hγP, b, hb, m, hm, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, gen]
    exact AddSubgroup.subset_closure ⟨γ, hγ, hγP, a, ha, m, hm, t, ht, rfl⟩
  have hmem : (fun k => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s k)) ∈ latV S N P :=
    AddSubgroup.subset_closure ⟨α, hα, hP, 1, rfl, s, hs, rfl⟩
  have h2 := AddSubgroup.mem_comap.1 (key (h hmem))
  rw [gen] at h2
  exact h2

set_option maxHeartbeats 2000000 in

theorem latV_le_of_local (S : HSp D) (N M : Lat S) (hN : Submodule.IsLattice D.host.E N)
    (hM : Submodule.IsLattice D.host.E M) (P : Pl D → Prop)
    (h : ∀ p, P p → latV S N (· = p) ≤ latV S M (· = p)) : latV S N P ≤ latV S M P := by
  classical
  obtain ⟨d, hd, hNM⟩ := exists_int_smul_le N M hN.fg hM.span_eq_top
  obtain ⟨B, hB⟩ : ∃ B : Finset (Pl D), ∀ w : Pl D, w ∉ B → ((d : 𝓞 D.host.F)) ∉ w.asIdeal :=
    ⟨(finite_places_int (D := D) d hd).toFinset, fun w hw h' => hw ((Set.Finite.mem_toFinset _).2 h')⟩
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, b, hb, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at hb
  subst hb
  let Ψ : Af D.host.F →+ (Fin S.rank → AE D) :=
    AddMonoidHom.mk' (fun β => fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) (by
      intro β β'
      funext i
      rw [Pi.add_apply, ← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (add_zero 0).symm rfl)
  have hsplit : α = ∑ v ∈ B, α * indQ D {v} + α * (1 - indQ D B) := by
    have e : indQ D B = ∑ v ∈ B, indQ D {v} := by simp only [indQ, Finset.sum_singleton]
    rw [← Finset.mul_sum, ← e, ← mul_add, add_sub_cancel, mul_one]
  show Ψ α ∈ latV S M P
  rw [hsplit, map_add, map_sum]
  refine add_mem (AddSubgroup.sum_mem _ fun v _ => ?_) ?_
  · by_cases hv : P v
    · have h1 : Ψ (α * indQ D {v}) ∈ latV S N (· = v) := by
        refine AddSubgroup.subset_closure ⟨α * indQ D {v}, fun w => ?_, fun w hw => ?_, 1, rfl, x, hx, rfl⟩
        · rw [map_mul, evalV_indQ]
          split_ifs
          · rw [mul_one]; exact hα w
          · rw [mul_zero]; exact zero_mem _
        · rw [map_mul, evalV_indQ, if_neg (by rwa [Finset.mem_singleton]), mul_zero]
      exact latV_mono' S M (fun w hw => hw ▸ hv) (h v hv h1)
    · have h0 : α * indQ D {v} = 0 := by
        apply RestrictedProduct.ext
        intro w
        change evalV D.host.F w (α * indQ D {v}) = evalV D.host.F w 0
        rw [map_mul, evalV_indQ, map_zero]
        split_ifs with hw
        · rw [Finset.mem_singleton] at hw
          subst hw
          rw [hP w hv, zero_mul]
        · rw [mul_zero]
      rw [h0, map_zero]
      exact zero_mem _
  · generalize hβ : α * (1 - indQ D B) = β
    have hβB : ∀ w, evalV D.host.F w β = if w ∈ B then 0 else evalV D.host.F w α := by
      intro w
      rw [← hβ, map_mul, map_sub, map_one, evalV_indQ]
      split_ifs
      · rw [sub_self, mul_zero]
      · rw [sub_zero, mul_one]
    have hsm : ∀ w, evalV D.host.F w (((d : D.host.F))⁻¹ • β) =
        algebraMap D.host.F (w.adicCompletion D.host.F) ((d : D.host.F))⁻¹ * evalV D.host.F w β := by
      intro w
      rw [map_smul, Algebra.smul_def]
    refine AddSubgroup.subset_closure ⟨((d : D.host.F))⁻¹ • β, fun w => ?_, fun w hw => ?_,
      1, rfl, d • x, hNM x hx, ?_⟩
    · by_cases hw : w ∈ B
      · rw [hsm, hβB, if_pos hw, mul_zero]
        exact zero_mem _
      · have hwv : ((d : 𝓞 D.host.F)) ∉ w.asIdeal := hB w hw
        have hval : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (d : D.host.F)) = 1 := by
          have h1 := (w.valuation_eq_one_iff_notMem (K := D.host.F)).mpr hwv
          have h2 := w.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))
          have h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F)) :=
            map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _
          exact h2.trans (h4 ▸ h1)
        have hαw := hα w
        have e1 : evalV D.host.F w β = evalV D.host.F w α := by rw [hβB, if_neg hw]
        rewrite [map_smul, e1]
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hαw ⊢
        rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
        exact hαw
    · have e0 : evalV D.host.F w β = 0 := by
        rw [hβB]
        split_ifs
        · rfl
        · exact hP w hw
      rewrite [map_smul, e0]
      exact smul_zero _
    · funext i
      show pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) =
        pairA D.host.F 0 (((d : D.host.F))⁻¹ • β) ⊗ₜ[D.host.F] (1 * (d • x i))
      exact pairA_tmul_int_gen d hd β (x i)

theorem latO_congr : ∀ (D : D7) (S T : HSp D) (N M : Lat S) (N' M' : Lat T), IsSelfDualC S N → IsSelfDualC S M →
    IsSelfDualC T N' → IsSelfDualC T M' → ∀ (P : Pl D → Prop),
    (∀ p, P p → latV S N (· = p) = latV S M (· = p) ∧ latV T N' (· = p) = latV T M' (· = p)) →
    latO S T (N : Set _) (N' : Set _) P = latO S T (M : Set _) (M' : Set _) P := by
  intro D S T N M N' M' hN hM hN' hM' P hloc
  have hS : latV S N P = latV S M P := le_antisymm
    (latV_le_of_local S N M hN.1 hM.1 P fun p hp => (hloc p hp).1.le)
    (latV_le_of_local S M N hM.1 hN.1 P fun p hp => (hloc p hp).1.ge)
  have hT : latV T N' P = latV T M' P := le_antisymm
    (latV_le_of_local T N' M' hN'.1 hM'.1 P fun p hp => (hloc p hp).2.le)
    (latV_le_of_local T M' N' hM'.1 hN'.1 P fun p hp => (hloc p hp).2.ge)
  apply le_antisymm
  · exact (latO_le_right S T _ N' M' P hT.le).trans (latO_le_left S T N M _ P hS.le)
  · exact (latO_le_right S T _ M' N' P hT.ge).trans (latO_le_left S T M N _ P hS.ge)

end GlobalTheory.FinPl.LatCong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionMovesByTranslatePairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeCompletion_moves_by_translatePair : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (g s : GA D S) (h s' : GA D T) N N' N₁ N₁', Moves S hS g N → Moves T hT h N' → Moves S hS (s * g) N₁ → Moves T hT (s' * h) N₁' → ∀ u : WO S T, u ∈ (latO S T (latFr S hS N₁) (latFr T hT N₁') fun _ => True) ↔ ∃ u₀ ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), u = actO S T s s' u₀ := by
  first | exact @GlobalTheory.LatPairMove.latO_move | exact GlobalTheory.LatPairMove.latO_move | (intros; apply GlobalTheory.LatPairMove.latO_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemAtUniqueOrth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.PlaceIdemUniq

theorem idemAt_unique_orth : ∀ (D : D7) (a b : AE D) (PP PP' : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt a PP → Formalism.L2.NTheta.IsIdemAt b PP' → (PP = PP' → a = b) ∧ (PP ≠ PP' → a * b = 0) := by
  intro D a b PP PP' ha hb
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact Formalism.IndefR.Fin.idemAt_eq_split (Formalism.IndefR.Fin.idemAt_split ha) ha hb
  · exact Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split ha) ha hb h

end GlobalTheory.PlaceIdemUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfEqRationalAddNsmulStandardHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.AdForm.DenseHalf

theorem half_eq_rat_add_nsmul : ∀ {D : D7} (S T : HSp D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ M : ℕ, 0 < M → ∀ w : WO S T, IsHalf e w → ∃ (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T ∧ IsHalf e v ∧ w = z.map (fun r => e * incA D r) + M • v := by
  intro D S T e P he M hM w hw
  obtain ⟨z, v, hv, hvh, h⟩ := GlobalTheory.AdForm.exists_rat_half_approx S T e P he M hM w
  refine ⟨z, -v, neg_mem hv, fun i j => ?_, ?_⟩
  · simp only [Matrix.neg_apply, mul_neg, hvh i j]
  · have hw' : e • w = w := by
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, hw i j]
    rw [h, hw', smul_neg]
    abel

end GlobalTheory.AdForm.DenseHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfMemCompletedHomLatticeIffLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.HalfLat
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D} {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_den {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e P) {r : D.host.E}
    (hr : finPart D (e * incA D r) ∈ intAE D) :
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (o : D.host.E) = s * r := by
  rcases (P.valuation D.host.E).val_le_one_or_val_inv_lt_one r with h | h
  · obtain ⟨n, d, hd⟩ := P.exists_primeCompl_mul_eq_of_integer r h
    exact ⟨d, d.2, n, by rw [mul_comm]; exact hd.symm⟩
  by_cases hr0 : r = 0
  · exact ⟨1, P.asIdeal.primeCompl.one_mem, 0, by simp [hr0]⟩
  obtain ⟨n, d, hd⟩ := P.exists_primeCompl_mul_eq_of_integer r⁻¹ h.le
  have hdP : (d : 𝓞 D.host.E) ∉ P.asIdeal := d.2
  have hd0 : (d : 𝓞 D.host.E) ≠ 0 := fun h => hdP (h ▸ zero_mem _)
  have hd0' : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => hd0 (RingOfIntegers.ext h)
  have hd' : r⁻¹ * ((d : 𝓞 D.host.E) : D.host.E) = (n : D.host.E) := hd
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (inv_ne_zero hr0) hd0' hd'
  have hnP : n ∈ P.asIdeal := by
    refine (P.valuation_lt_one_iff_mem (K := D.host.E) n).1 ?_
    change P.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E n) < 1
    rw [← hd, Valuation.map_mul]
    exact mul_lt_one_of_lt_of_le h (P.valuation_le_one _)
  have h1 : finPart D (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hdP ((he.2 _ hd0).2 h)
  refine absurd ?_ ((he.2 _ hn0).1 hnP)
  have h2 := GlobalTheory.HeckeConj.mul_mem_intAE D hr h1
  rwa [← RingHom.map_mul, mul_mul_mul_comm, he.1.1, ← RingHom.map_mul, ← inv_inv r, ← mul_inv, hd'] at h2

noncomputable def form (S : HSp D) (s : Fin S.rank → D.host.E) : (Fin S.rank → D.host.E) →ₗ[D.host.E] D.host.E :=
  ∑ i, ∑ j, (star (s i) * S.gram i j) • LinearMap.proj j

theorem form_apply (s v : Fin S.rank → D.host.E) : form S s v = ∑ i, ∑ j, star (s i) * S.gram i j * v j := by
  simp [form, LinearMap.sum_apply]

theorem expand {n : ℕ} {s s' : Fin n → Fin S.rank → D.host.E}
    (h : ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0) (v : Fin S.rank → D.host.E) :
    v = ∑ k, form S (s' k) v • s k := by
  funext a
  have h1 : v a = ∑ j, (∑ i, s i a * ∑ k, star (s' i k) * S.gram k j) * v j := by simp [h]
  rw [h1, Finset.sum_apply]
  simp only [form_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

noncomputable def coefA (S T : HSp D) (b : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    WO S T →+ AE D :=
  AddMonoidHom.mk' (fun u => ∑ i, ∑ j, ∑ m, incA D (b * (star (t i) * T.gram i j) * s m) * u j m) fun x y => by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem coefA_apply (b : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (u : WO S T) :
    coefA S T b s t u = ∑ i, ∑ j, ∑ m, incA D (b * (star (t i) * T.gram i j) * s m) * u j m := rfl

theorem coefA_int (hN : IsSelfDualC S N) (hN' : IsSelfDualC T N') {b : D.host.E}
    (hb : ∀ a ∈ D.host.AA, ∃ c : 𝓞 D.host.E, (c : D.host.E) = a * b)
    {s : Fin S.rank → D.host.E} (hs : s ∈ N) {t : Fin T.rank → D.host.E} (ht : t ∈ N') {u : WO S T}
    (hu : u ∈ latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) :
    finPart D (coefA S T b s t u) ∈ intAE D := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s0, hs0, t0, ht0, rfl⟩ := hw
    obtain ⟨c, hc'⟩ := hb a ha
    obtain ⟨o, ho⟩ := (hN.2 s).1 hs s0 hs0
    obtain ⟨o', ho'⟩ := (hN'.2 t0).1 ht0 t ht
    refine AddSubgroup.subset_closure ⟨α, hα, c * o' * o, ?_⟩
    have h1 : ∀ x y : D.host.E, incA D x * (pairA D.host.F 0 α ⊗ₜ[D.host.F] y) =
        pairA D.host.F 0 α ⊗ₜ[D.host.F] (x * y) := fun x y => by
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : ((c * o' * o : 𝓞 D.host.E) : D.host.E) = ∑ i, ∑ j, ∑ m, (b * (star (t i) * T.gram i j) * s m) *
        (a * t0 j * ∑ k, star (s0 k) * S.gram k m) := by
      have h3 : ((c * o' * o : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) * o' * o := by
        simp only [map_mul]
      rw [h3, hc', ho, ho', Finset.sum_comm (f := fun i j => star (s0 i) * S.gram i j * s j), Finset.mul_sum (a := a * b),
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum (a := a * b), Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_mul]
      ring
    rw [coefA_apply]
    simp only [Matrix.of_apply, h1, ← TensorProduct.tmul_sum]
    rw [h2]
    rfl
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, RingHom.map_neg]; exact neg_mem hx

theorem coefA_rat (e : AE D) (b : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E)
    (x : Formalism.L2.Col.HomE D.host.E S.rank T.rank) :
    coefA S T b s t ((LinearMap.toMatrix' x).map fun r => e * incA D r) = e * incA D (b * form T t (x s)) := by
  rw [coefA_apply, form_apply, ← LinearMap.toMatrix'_mulVec x s]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.map_apply, mul_left_comm, ← RingHom.map_mul]
  congr 2
  ring

set_option maxHeartbeats 1000000 in

theorem mem_localization_of_component (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) (hN' : IsSelfDualC T N') {e e' : AE D}
    {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e' P) (hee : e' * e = e')
    {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : ((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S N hN
  obtain ⟨m, t, t', ht, htt⟩ := GlobalTheory.LatVacDual.dualFamily D T N' hN'
  have hxe : x = ∑ k, ∑ i, form T (t' i) (x (s k)) • (form S (s' k)).smulRight (t i) := by
    refine LinearMap.ext fun v => ?_
    conv_lhs => rw [expand hss v, map_sum]
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_lhs => rw [map_smul, expand htt (x (s k)), Finset.smul_sum]
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D)
  have h1 : (1 : D.host.E) ∈ D.host.AA0 * (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [Formalism.BasicNotions.Host.AA0, inv_mul_cancel₀ hb0]
    exact FractionalIdeal.one_mem_one _
  rw [← one_smul D.host.E x]
  refine FractionalIdeal.mul_induction_on (C := fun c => c • x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal
    (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) h1 (fun a ha b hb => ?_)
    fun a b ha hb => by rw [add_smul]; exact add_mem ha hb
  have hb' : ∀ a ∈ D.host.AA, ∃ c : 𝓞 D.host.E, (c : D.host.E) = a * b := fun a ha => by
    rw [Formalism.BasicNotions.Host.AA, Formalism.BasicNotions.Host.ccE, hc, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul] at ha
    have h := FractionalIdeal.mul_mem_mul ha hb
    rw [Formalism.BasicNotions.Host.AA0, inv_mul_cancel₀ hb0] at h
    exact (FractionalIdeal.mem_one_iff _).1 h
  have hi : finPart D e' ∈ intAE D := by
    by_contra h
    refine P.asIdeal.primeCompl.one_mem ((he.2 1 one_ne_zero).2 ?_)
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one]
  rw [hxe, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  rw [Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  have h2 := GlobalTheory.HeckeConj.mul_mem_intAE D hi (coefA_int hN hN' hb' (hs k).1 (ht i).2 hx)
  rw [coefA_rat, ← RingHom.map_mul, ← mul_assoc, hee] at h2
  obtain ⟨d, hd, o, ho⟩ := exists_den he h2
  refine ⟨d, hd, ?_⟩
  have h3 : a • (form S (s' k)).smulRight (t i) ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
    refine Submodule.subset_span ⟨a, ha, _, fun v hv => ?_, rfl⟩
    obtain ⟨c, hc⟩ := (hN.2 v).1 hv _ (hs k).2
    rw [LinearMap.smulRight_apply, form_apply, ← hc]
    exact N'.smul_mem c (ht i).1
  convert Submodule.smul_mem _ o h3 using 1
  rw [← IsScalarTower.algebraMap_smul D.host.E d, ← IsScalarTower.algebraMap_smul D.host.E o,
    show algebraMap _ D.host.E o = _ from ho, smul_smul, smul_smul, smul_smul]
  congr 1
  change (d : D.host.E) * _ * _ = _
  ring

theorem comp_mem (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) :
    ((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : s ∉ P.asIdeal := hs
  have hne : s ≠ 0 := fun h => hs' (h ▸ zero_mem _)
  have hs0 : (s : D.host.E) ≠ 0 := fun h => hne (RingOfIntegers.ext h)
  have h1 : finPart D (e * incA D ((s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hs' ((he.2 _ hne).2 h)
  have h4 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ h1 _
    (finTens_mem_latO (one_mem_intAf _) (HalfPairing.toMatrix_mem_latRat hc hN hsx))
  convert h4 using 1
  ext i j
  have h5 := GlobalTheory.SplitScalar.infPart_splitIdem he.1
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h5, zero_mul]) ?_
  have h6 : finPart D (finTens 1 (LinearMap.toMatrix' (s • x)) i j) =
      finPart D (incA D ((s : D.host.E) * LinearMap.toMatrix' x i j)) := rfl
  rw [RingHom.map_mul (finPart D) (_ * _), h6, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D),
    inv_mul_cancel_left₀ hs0]

theorem half_mem_latO_iff : ∀ (D : D7) (S T : HSp D), D.host.ccK = ⊤ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, (((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∀ P ∈ SS, x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) := by
  intro D S T hc e SS he N N' hN hN' x
  constructor
  · intro hx P hP
    obtain ⟨a, ha, hae⟩ := GlobalTheory.OffIdem.idemSum_mul_idemAt he hP
    exact mem_localization_of_component hc hN hN' ha hae hx
  · intro hx
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
    have e1 : ((LinearMap.toMatrix' x).map fun r => (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' x).map fun r => es PP * incA D r : WO S T) := by
      ext i j
      rw [Matrix.map_apply, Matrix.sum_apply, Finset.sum_mul]
      rfl
    rw [e1]
    exact sum_mem fun PP hPP => comp_mem hc hN (hes PP hPP) (hx PP hPP)

end GlobalTheory.AdForm.HalfLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumDisjointUnion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.IdemSumAdd

theorem idemSum_union : ∀ (D : D7) (a b : AE D) (P Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), Disjoint P Q → (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → IsIdemSum a P → IsIdemSum b (P ∪ Q) → b = a + ∑ PP ∈ Q, es PP := by
  intro D a b P Q es hPQ hQ ha hb
  rw [← GlobalTheory.ExportSeries.idem_eq ha, ← GlobalTheory.ExportSeries.idem_eq hb, GlobalTheory.ExportSeries.idem,
    GlobalTheory.ExportSeries.idem, Finset.sum_union hPQ]
  congr 1
  exact Finset.sum_congr rfl fun PP hPP => GlobalTheory.ExportSeries.idemAt_eq (hQ PP hPP)

end GlobalTheory.IdemSumAdd
end

