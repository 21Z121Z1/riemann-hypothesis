import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1271
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicExtremalNegativeFirst
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

open GlobalTheory.HolDict.ModelRep in

theorem isHolFor_extVec_holPar : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (h : D.what₂.Tau → HCParam D.R) (p q : ℕ), IsInfFam θ → p + q = D.R.r → V.rank = D.R.r → (∀ ρ, S ρ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q)) → ∀ v : M.Vec, IsExtVec M v → ∃ x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, NegFirst V q x ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → IsHolFor θ V x (fun ρ c => wtCol (h ρ) p q c) (T v) := by
  intro D θ V S M h p q hθ hpq hr hS v hv
  have hn : p + q = V.rank := hpq.trans hr.symm
  have hp : p ≤ V.rank := by omega
  have he : ∀ ρ, IsEnum (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q)) (M.lam ρ) (M.ε ρ) :=
    fun ρ => hS ρ ▸ M.enum ρ
  have hok := fun ρ => Formalism.L2.NTheta.holOK_kapW (h ρ) p q hpq
  have hε : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < p) := fun ρ a => by
    obtain ⟨hn', hx⟩ := GlobalTheory.HolDS.enum_holPar (hok ρ) (he ρ)
    by_cases ha : (a : ℕ) < p
    · have := (hx (Sum.inl ⟨a, ha⟩)).2
      rw [show Fin.cast hn' (finSumFinEquiv (Sum.inl ⟨a, ha⟩ : Fin p ⊕ Fin q)) = a from Fin.ext (by simp)] at this
      simp [this, ha]
    · have := (hx (Sum.inr ⟨a - p, by have := a.2; omega⟩)).2
      rw [show Fin.cast hn' (finSumFinEquiv (Sum.inr ⟨a - p, by have := a.2; omega⟩ : Fin p ⊕ Fin q)) = a from
        Fin.ext (by simp; omega)] at this
      simp [this, ha]
  have hq : ∀ ρ, nNeg (M.ε ρ) = q := fun ρ => by rw [nNeg_shape hp (hε ρ)]; omega
  have hw : ∀ ρ c, extWt M ρ (arr (nNeg (M.ε ρ)) c) = (wtCol (h ρ) p q c : ℝ) := fun ρ c => by
    obtain ⟨hn', hx⟩ := GlobalTheory.HolDS.lowK_holPar (hok ρ) (he ρ)
    have hc := c.2
    by_cases hcq : (c : ℕ) < q
    · rw [extWt_arr M ρ hp (hε ρ) c (Fin.cast hn' (finSumFinEquiv (Sum.inr ⟨c, hcq⟩ : Fin p ⊕ Fin q)))
        (by rw [if_pos (by omega)]; simp), hx]
      simp only [wtCol, if_pos hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inr]
    · rw [extWt_arr M ρ hp (hε ρ) c (Fin.cast hn' (finSumFinEquiv (Sum.inl ⟨c - q, by omega⟩ : Fin p ⊕ Fin q)))
        (by rw [if_neg (by omega)]; simp; omega), hx]
      simp only [wtCol, if_neg hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inl]
  have hneg : NegFirst V q (x0Mat M) := fun ρ => by
    have := orth_sub (M.fr_unit ρ) (M.fr_gram ρ) (arr (nNeg (M.ε ρ)))
    refine this.trans ?_
    unfold Formalism.REAL.Jm
    rw [Matrix.submatrix_diagonal _ _ (arr_injective (nNeg_le (M.ε ρ)))]
    congr 1
    funext a
    have := a.2
    simp only [Function.comp, hε, hq, arr, decide_eq_true_eq]
    split_ifs <;> first | rfl | (exfalso; simp only at *; omega)
  refine ⟨x0Mat M, hneg, fun J χ T hT => ⟨(hT.aut v).smooth, fun ρ c d hcd => ?_, fun ρ t g => ?_⟩⟩
  · have hk := (GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ p true (fun a => by rw [hε]; by_cases ha : (a : ℕ) < p <;> simp [ha])).1
    have e := conj_single (M.fr_unit ρ) (arrEquiv (nNeg_le (M.ε ρ))) c d
    change x0Mat M ρ * _ * (x0Mat M ρ)⁻¹ =
      _ * Matrix.single (arr (nNeg (M.ε ρ)) c) (arr (nNeg (M.ε ρ)) d) 1 * _ at e
    rw [e]
    apply hk
    have h1 : (c : ℕ) < d := hcd
    have h2 := d.2
    simp only [KillPair, hε, hq, arr, Fin.lt_def, decide_eq_true_eq, decide_eq_false_iff_not, ne_eq, decide_eq_decide]
    split_ifs <;> simp only <;> omega
  · have hk := (GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ p true (fun a => by rw [hε]; by_cases ha : (a : ℕ) < p <;> simp [ha])).2
    set e := arrEquiv (nNeg_le (M.ε ρ)) with hedef
    have hx : IsUnit (x0Mat M ρ).det := by
      have h1 := congrArg Matrix.det (hneg ρ)
      rw [det_mul, det_diagonal] at h1
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      rw [h0, mul_zero] at h1
      exact Finset.prod_ne_zero_iff.2 (fun a _ => by split_ifs <;> simp) h1.symm
    have h1 := torus_x0Mat M ρ fun a => Complex.exp ((t (e.symm a) : ℂ) * Complex.I)
    have h2 : ∀ c, e.symm (arr (nNeg (M.ε ρ)) c) = c := fun c => e.symm_apply_apply c
    simp only [h2] at h1
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hx, hk (fun a => t (e.symm a)) g, ← e.sum_comp]
    simp only [Equiv.symm_apply_apply]
    congr 5
    funext c
    rw [← hw ρ c]
    rfl

end GlobalTheory.HolRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceNormGramInverseEqMulMatrix
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat

theorem nrmL_dlt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u β : B.A, IsUnit (GlobalTheory.TwLat.gram e b β) → B.σ β = β * ((-1) ^ (m - 1) * u) → (nrmL m w (GlobalTheory.TwLat.dlt e b β)).val = GlobalTheory.TwLat.mulMat e b u := by
  intro E _ _ _ _ w hw K e hec _ _ B m b u β hG hβ
  let B' : GlobalTheory.UnitLemma.InvAlg K := { B with g := u }
  have hGc0 := GlobalTheory.GramTwistNorm.gram_map_conj B' (w.adicCompletion E) e (cj w) hec m β hβ b
  set G := gram e b β with hGdef
  set P := mulMat e b u with hP
  set Φ := GlobalTheory.Tw.Phi m (w.adicCompletion E) with hΦ
  set s : w.adicCompletion E := (-1) ^ (m - 1) with hs
  have hGc : G.map (cj w) = s • (Gᵀ * P) := hGc0
  have hGd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hΦT : Φᵀ * Φ = 1 := mul_eq_one_comm.1 (GlobalTheory.GramTwistNorm.phi_mul_transpose m)
  have hd : (dlt e b β).val = (G⁻¹)ᵀ * Φᵀ := by
    rw [dlt, dif_pos hG]
    change ((hG.unit⁻¹ : (Matrix (Fin m) (Fin m) (w.adicCompletion E))ˣ).val)ᵀ * Φᵀ = _
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
  have hdi : ((dlt e b β)⁻¹).val = Φ * Gᵀ := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hd, Matrix.mul_assoc, ← Matrix.mul_assoc Φᵀ, hΦT, Matrix.one_mul, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv G hGd, Matrix.transpose_one]
  have hΦΦ : Φᵀ * Φᵀ = s • (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
    rw [← Matrix.transpose_mul, hΦ, GlobalTheory.GramTwistNorm.phi_mul_self, Matrix.transpose_smul, Matrix.transpose_one]
  have hθ : (thetaGL m (cj w) (dlt e b β)).val = Φ * (((dlt e b β)⁻¹).val.map (cj w))ᵀ * Φᵀ := rfl
  have hGG : (G⁻¹)ᵀ * Gᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv G hGd, Matrix.transpose_one]
  have hss : s * s = 1 := by rw [hs, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [nrmL, if_neg hw, Units.val_mul, hθ, hdi, Matrix.map_mul, hΦ, GlobalTheory.GramTwistNorm.phi_map, ← hΦ,
    Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose, hGc, hd]
  calc (G⁻¹)ᵀ * Φᵀ * (Φ * (s • (Gᵀ * P) * Φᵀ) * Φᵀ)
      = s • (((G⁻¹)ᵀ * Gᵀ) * P * (Φᵀ * Φᵀ)) + (0 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
        rw [add_zero]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Φᵀ Φ, hΦT, Matrix.one_mul]
    _ = P := by
        rw [add_zero, hGG, hΦΦ, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hss, one_smul]

end GlobalTheory.TwLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfFixedVectorsAdelicLevelNeBotOfLocalLevel
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixLev
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ext_fin {x y : UA E n} (hx : x ∈ finU E n) (hy : y ∈ finU E n) (h : ∀ v : Pl E, cLoc v x = cLoc v y) : x = y := by
  have hx' : cInf x = 1 := hx
  have hy' : cInf y = 1 := hy
  apply Subtype.ext
  apply ga_ext
  · exact hx'.trans hy'.symm
  · exact Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v =>
      by
        have := congrArg (fun z : GLw n v => (z : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j) (h v)
        exact this)

theorem integral_eventually (g : UA E n) : ∀ᶠ v in cofinite, ∀ i j : Fin n,
    (cLoc v g) i j ∈ v.adicCompletionIntegers E ∧ (cLoc v g)⁻¹ i j ∈ v.adicCompletionIntegers E := by
  have h1 : ∀ x : Af E, ∀ᶠ v in cofinite, pLoc E v x ∈ v.adicCompletionIntegers E := fun x => x.2
  have h2 : ∀ i j : Fin n, ∀ᶠ v in cofinite,
      (cLoc v g) i j ∈ v.adicCompletionIntegers E ∧ (cLoc v g)⁻¹ i j ∈ v.adicCompletionIntegers E := by
    intro i j
    filter_upwards [h1 (pFin E ((g : GA E n) i j)), h1 (pFin E (((g⁻¹ : UA E n) : GA E n) i j))] with v hv hv'
    refine ⟨hv, ?_⟩
    rw [← map_inv]
    exact hv'
  exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 (h2 i)

def fib (B : Finset (Pl E)) : Set (Pl E) :=
  {u | ∃ t ∈ B, u.under (𝓞 (maximalRealSubfield E)) = t.under (𝓞 (maximalRealSubfield E))}

theorem fib_closed (B : Finset (Pl E)) (u v : Pl E)
    (h : u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E))) (hu : u ∈ fib B) : v ∈ fib B := by
  obtain ⟨t, ht, e⟩ := hu
  exact ⟨t, ht, h.symm.trans e⟩

def stabU (φ : UA E n → ℂ) : Subgroup (UA E n) where
  carrier := {x | RU E n x φ = φ}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem one_entry_mem (v : Pl E) (i j : Fin n) : (1 : GLw n v) i j ∈ v.adicCompletionIntegers E := by
  change (1 : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j ∈ _
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem local_fixed (S : Set (Pl E)) (hS : IsSection S) (K' : ∀ w : Pl E, Subgroup (UL n w)) (φ : UA E n → ℂ)
    (hφ : ∀ w ∈ S, ∀ x ∈ locU n w, (∃ k ∈ K' w, k.1 = cLoc w x) → RU E n x φ = φ) (B : Finset (Pl E)) :
    ∀ h : UA E n, h ∈ finU E n → (∀ w ∈ S, ∃ k ∈ K' w, k.1 = cLoc w h) → (∀ v, v ∉ fib B → cLoc v h = 1) →
      h ∈ stabU φ := by
  induction B using Finset.induction_on with
  | empty =>
    intro h hfin _ h1
    have : h = 1 := ext_fin hfin (one_mem _) fun v => by
      rw [h1 v (by rintro ⟨t, ht, _⟩; simp at ht), map_one]
    rw [this]
    exact one_mem _
  | insert t B _ ih =>
    intro h hfin hK h1
    obtain ⟨wt, ⟨hwtS, hwt⟩, _⟩ := hS t
    obtain ⟨x, hxfin, hx⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion E n (fib {t}) (fib_closed {t}) h hfin
    have hxloc : x ∈ locU n wt := by
      refine Subgroup.mem_inf.2 ⟨hxfin, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
      rw [MonoidHom.mem_ker, hx u, if_neg]
      rintro ⟨t', ht', e⟩
      rw [Finset.mem_singleton] at ht'
      subst ht'
      exact hu (e.trans hwt.symm)
    have hwtf : wt ∈ fib {t} := ⟨t, Finset.mem_singleton_self t, hwt⟩
    have hxS : x ∈ stabU φ := by
      obtain ⟨k, hk, hkx⟩ := hK wt hwtS
      refine hφ wt hwtS x hxloc ⟨k, hk, ?_⟩
      rw [hx wt, if_pos hwtf, hkx]
    have hrest : x⁻¹ * h ∈ stabU φ := by
      refine ih _ (mul_mem (inv_mem hxfin) hfin) ?_ ?_
      · intro w hw
        rw [map_mul, map_inv, hx w]
        split_ifs
        · exact ⟨1, one_mem _, by rw [inv_mul_cancel]; rfl⟩
        · rw [inv_one, one_mul]; exact hK w hw
      · intro v hv
        rw [map_mul, map_inv, hx v]
        split_ifs with hvt
        · exact inv_mul_cancel _
        · rw [inv_one, one_mul]
          refine h1 v ?_
          rintro ⟨t', ht', e⟩
          rcases Finset.mem_insert.1 ht' with rfl | ht'
          · exact hvt ⟨t', Finset.mem_singleton_self _, e⟩
          · exact hv ⟨t', ht', e⟩
    have : h = x * (x⁻¹ * h) := by group
    rw [this]
    exact mul_mem hxS hrest

theorem inf_fixed_globLev_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S →
    ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → HasLevel S π K' → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ := by
  intro E _ _ _ n S hS K' _ π hπ hL
  obtain ⟨φ, hφπ, hφ0, hφfix⟩ := hL
  have hlev := (hπ.aut φ hφπ).level
  have key : ∀ g : finU E n, g ∈ globLev S K' → (g : UA E n) ∈ stabU φ := by
    intro g hg
    have hgS : ∀ w ∈ S, ∃ k ∈ K' w, k.1 = cLoc w (g : UA E n) := by
      intro w hw
      have h1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg w) hw
      rw [Subgroup.mem_comap] at h1
      obtain ⟨k, hk, e⟩ := Subgroup.mem_map.1 h1
      exact ⟨k, hk, e⟩
    obtain ⟨T, hT⟩ := GlobalTheory.T.mem_open_nhd_one_of_integral_eq_one_on_finset E n _ hlev (by simp)
    have hbad := Filter.eventually_cofinite.1 (integral_eventually (g : UA E n))
    let B : Finset (Pl E) := T ∪ hbad.toFinset
    obtain ⟨x, hxfin, hx⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion E n (fib B) (fib_closed B) (g : UA E n) g.2
    have hxS : x ∈ stabU φ := by
      refine local_fixed S hS K' φ hφfix B x hxfin ?_ ?_
      · intro w hw
        rw [hx w]
        split_ifs
        · exact hgS w hw
        · exact ⟨1, one_mem _, rfl⟩
      · intro v hv
        rw [hx v, if_neg hv]
    have hc : ∀ v, cLoc v (x⁻¹ * (g : UA E n)) = if v ∈ fib B then 1 else cLoc v (g : UA E n) := by
      intro v
      rw [map_mul, map_inv, hx v]
      split_ifs
      · exact inv_mul_cancel _
      · rw [inv_one, one_mul]
    have hint : ∀ v, v ∉ fib B → ∀ i j : Fin n, (cLoc v (g : UA E n)) i j ∈ v.adicCompletionIntegers E ∧
        (cLoc v (g : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E := by
      intro v hv
      by_contra hc'
      exact hv ⟨v, Finset.mem_union_right _ (hbad.mem_toFinset.2 hc'), rfl⟩
    have hrest : x⁻¹ * (g : UA E n) ∈ stabU φ := by
      have := hT ⟨x⁻¹ * (g : UA E n), mul_mem (inv_mem hxfin) g.2⟩ ?_ ?_ ?_
      · exact this
      · intro v hv
        change cLoc v (x⁻¹ * (g : UA E n)) = 1
        rw [hc v, if_pos ⟨v, Finset.mem_union_left _ hv, rfl⟩]
      · intro v i j
        change (cLoc v (x⁻¹ * (g : UA E n))) i j ∈ _
        rw [hc v]
        split_ifs with hv
        · exact one_entry_mem v i j
        · exact (hint v hv i j).1
      · intro v i j
        change (cLoc v (x⁻¹ * (g : UA E n)))⁻¹ i j ∈ _
        rw [hc v]
        split_ifs with hv
        · rw [inv_one]; exact one_entry_mem v i j
        · exact (hint v hv i j).2
    have : (g : UA E n) = x * (x⁻¹ * (g : UA E n)) := by group
    rw [this]
    exact mul_mem hxS hrest
  intro hbot
  have hmem : φ ∈ π ⊓ fixed (RF E n) (globLev S K') := by
    refine ⟨hφπ, ?_⟩
    intro h
    change RU E n ((h : finU E n) : UA E n) φ = (1 : ℂˣ) • φ
    rw [one_smul]
    exact key h h.2
  rw [hbot] at hmem
  exact hφ0 ((Submodule.mem_bot ℂ).1 hmem)

end GlobalTheory.FixLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinityTypeUnitaryHeckeCharCMRestrictingToEtaStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinityType_unitaryHeckeCharCM_restricting_to_eta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E), μ.IsUnitary →
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    ∃ e : InfinitePlace E → ℤ, (∀ v, Odd (e v)) ∧
      ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v := by
  first | exact @GlobalTheory.MuInfType.infType | exact GlobalTheory.MuInfType.infType | (intros; apply GlobalTheory.MuInfType.infType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompLinearMapMatrixNonarchLocalFieldStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_comp_linearMap_matrix_nonarchLocalField : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : ℕ) (L : Matrix (Fin a) (Fin b) F →ₗ[F] Matrix (Fin a) (Fin b) F) (hL : LinearMap.det L ≠ 0) (φ : Matrix (Fin a) (Fin b) F → ℂ) (μ : @MeasureTheory.Measure (Matrix (Fin a) (Fin b) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫ x, φ (L x) ∂μ = ((((MeasureTheory.distribHaarChar F (Units.mk0 _ hL) : NNReal) : ℝ) : ℂ))⁻¹ * ∫ x, φ x ∂μ := by
  first | exact @GlobalTheory.DetScale.integral_comp_matrix | exact GlobalTheory.DetScale.integral_comp_matrix | (intros; apply GlobalTheory.DetScale.integral_comp_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarJacobianDetEqZeroOfCompactSupport
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem contDiffOn_dbar_apply {n : ℕ} {U : Set (V n)} {f : V n → ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (ξ : V n) : ContDiffOn ℝ 1 (fun x => dbar f x ξ) U := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y) U := hf.fderiv_of_isOpen hU (by norm_num)
  have ha : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y ξ) U := h1.clm_apply contDiffOn_const
  have hb : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y (Complex.I • ξ)) U :=
    h1.clm_apply contDiffOn_const
  have : (fun x => dbar f x ξ) =
      fun x => (1 / 2 : ℂ) • (fderiv ℝ f x ξ + Complex.I • fderiv ℝ f x (Complex.I • ξ)) := by
    funext x; exact dbar_apply f x ξ
  rw [this]
  exact (ha.add (hb.const_smul Complex.I)).const_smul _

theorem integral_dbarJacobian_eq_zero : ∀ {n : ℕ} (U K : Set (V n)) (f : Fin n → V n → ℂ) (j : Fin n),
    IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (f i) U) →
    (∀ v ∈ U, v ∉ K → f j v = 0) →
    ∫ v in U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  intro n U K f j hU hK hKU hf hz
  have hgC : ∀ w : Equiv.Perm (Fin n), ContDiffOn ℝ 1
      (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) U := fun w =>
    ((hf j).of_le (by norm_num)).mul
      (contDiffOn_prod fun i _ => contDiffOn_dbar_apply hU (hf i) _)
  have hg0 : ∀ w : Equiv.Perm (Fin n), ∀ v ∈ U, v ∉ K →
      (f j v * ∏ i ∈ Finset.univ.erase j, dbar (f i) v (coordVec (w i))) = 0 :=
    fun w v hv hvK => by rw [hz v hv hvK, zero_mul]
  have hT := fun w : Equiv.Perm (Fin n) =>
    GlobalTheory.T.integral_antiholomorphicDeriv_compactSupport_eq_zero U K _ (coordVec (w j)) hU hK hKU (hgC w) (hg0 w)
  have hcongr : ∫ v in U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det =
      ∫ v in U, ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) *
        dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v
          (coordVec (w j)) :=
    setIntegral_congr_fun hU.measurableSet fun v hv =>
      GlobalTheory.T.det_wirtingerAntiholomorphicDeriv_eq_sum f j v fun i => (hf i).contDiffAt (hU.mem_nhds hv)
  rw [hcongr, integral_finsetSum _ fun w _ => (hT w).1.const_mul _]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [integral_const_mul, (hT w).2, mul_zero]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqRankOneFactorSL2OfGeometricOnShellsStatement
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_rankOneFactorSL2_of_geometric_on_shells : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℕ), 2 ≤ q → ∀ (a : ℂ), ‖a‖ < 1 →
    ∀ (H : ℕ → Set X), (∀ j, MeasurableSet (H j)) → Monotone H → ⋃ j, H j = Set.univ →
    (∀ j, μ (H j) = (q : ENNReal) ^ j) → ∀ (F : X → ℂ), (∀ x ∈ H 0, F x = 1) →
    (∀ j x, x ∈ H (j + 1) → x ∉ H j → F x = (a / q) ^ (j + 1)) →
    Integrable F μ ∧ ∫ x, F x ∂μ = cSL q a ∧ ∫⁻ x, ‖F x‖ₑ ∂μ = ‖cSL q ((‖a‖ : ℝ) : ℂ)‖ₑ := by
  first | exact @GlobalTheory.integral_geometric_shells | exact GlobalTheory.integral_geometric_shells | (intros; apply GlobalTheory.integral_geometric_shells <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFiniteSumTopFormsStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_finite_sum_topForms : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {ι : Type} [Fintype ι] {d : ι → κ → Y → ℝ} {t : ι → ℝ}, (∀ a, IsTopForm e (d a) S) → (∀ a, HasInt e (d a) S (t a)) → HasInt e (fun i y => ∑ a, d a i y) S (∑ a, t a) := by
  first | exact @GlobalTheory.GoodTop.hasInt_sum | exact GlobalTheory.GoodTop.hasInt_sum | (intros; apply GlobalTheory.GoodTop.hasInt_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitsOfIsCompactClosureZpowersMulStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnits_of_isCompact_closure_zpowers_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (a : B.Aˣ), IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwLat.mulU e b a) : Set (GLw m w))) → a ∈ GlobalTheory.UnitLemma.intUnits K.O B.A := by
  first | exact @GlobalTheory.TwLat.mem_intUnits_of_isCompact_closure_zpowers | exact GlobalTheory.TwLat.mem_intUnits_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.TwLat.mem_intUnits_of_isCompact_closure_zpowers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberGlobalSectionEqSumCycleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_globalSection_eq_sum_cycle : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ X) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (s : M.Sec) (hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfSec hM s hs).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  first | exact @GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult | exact GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult | (intros; apply GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberNonnegOfNefAmpleAddNefStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_nonneg_of_nef_ample_add_nef : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → (∀ A N : LB X, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k F P := by
  first | exact @GlobalTheory.interNum_nonneg_of_isNef_of_ample_tens_nef | exact GlobalTheory.interNum_nonneg_of_isNef_of_ample_tens_nef | (intros; apply GlobalTheory.interNum_nonneg_of_isNef_of_ample_tens_nef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefOfNonzeroSectionPowInductionStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_tensor_nef_of_nonzeroSectionPow_induction : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ A M : LB X, IsAmpleLB A → IsNef k M → (∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r)) → IsAmpleLB (tens A M) := by
  first | exact @GlobalTheory.isAmpleLB_tens_of_nef_of_hasNonzeroSec_pow_step | exact GlobalTheory.isAmpleLB_tens_of_nef_of_hasNonzeroSec_pow_step | (intros; apply GlobalTheory.isAmpleLB_tens_of_nef_of_hasNonzeroSec_pow_step <;> assumption)
end

