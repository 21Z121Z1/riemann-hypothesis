import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliarySquarefreeLevelTwistPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0812
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AutomorphicArithmetic.LocalEmbeddings.BadRepAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LaHatMod

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

theorem valued_algebraMap (w : HeightOneSpectrum ℤ) (q : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) q) = w.valuation ℚ q :=
  valuedAdicCompletion_eq_valuation' w q

theorem exists_int_valued_sub_le (w : HeightOneSpectrum ℤ) {x : w.adicCompletion ℚ} (hx : Valued.v x ≤ 1)
    {c : ℚ} (hc0 : c ≠ 0) (hc : w.valuation ℚ c ≤ 1) :
    ∃ r : ℤ, Valued.v (x - (r : w.adicCompletion ℚ)) ≤ w.valuation ℚ c := by
  set c' : w.adicCompletion ℚ := algebraMap ℚ (w.adicCompletion ℚ) c
  have hc' : c' ≠ 0 := by
    simp only [c', ne_eq, map_eq_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective]; exact hc0
  have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v c' := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc')
  have hU : IsOpen ((fun y => (y - x) / c') ⁻¹' (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) :=
    (Valued.isOpen_valuationSubring _).preimage ((continuous_id.sub continuous_const).div_const c')
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (K := ℚ) w).exists_mem_open hU
    ⟨x, by simp [SetLike.mem_coe, sub_self, zero_div]⟩
  have hk' : Valued.v (x - algebraMap ℚ (w.adicCompletion ℚ) k) ≤ w.valuation ℚ c := by
    have h : Valued.v ((algebraMap ℚ (w.adicCompletion ℚ) k - x) / c') ≤ 1 := hk
    rw [map_div₀, div_le_one₀ hpos] at h
    rw [Valuation.map_sub_swap, ← valued_algebraMap]; exact h
  have hk1 : w.valuation ℚ k ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap ℚ (w.adicCompletion ℚ) k = x - (x - algebraMap ℚ (w.adicCompletion ℚ) k) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hx (hk'.trans hc))
  have hne : w.valuation ℚ c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer w hk1 (Units.mk0 _ hne)
  refine ⟨r, ?_⟩
  have hr' : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (k - algebraMap ℤ ℚ r)) ≤ w.valuation ℚ c := by
    rw [valued_algebraMap, Valuation.map_sub_swap]; exact hr.le
  have e : x - (r : w.adicCompletion ℚ) =
      (x - algebraMap ℚ (w.adicCompletion ℚ) k) + algebraMap ℚ (w.adicCompletion ℚ) (k - algebraMap ℤ ℚ r) := by
    rw [map_sub, algebraMap_int_eq, eq_intCast, map_intCast]; ring
  rw [e]
  exact (Valuation.map_add _ _ _).trans (max_le hk' hr')

variable {p : ℕ} [Fact p.Prime]

theorem valued_intCast (w : HeightOneSpectrum ℤ) (z : ℤ) :
    Valued.v ((z : w.adicCompletion ℚ)) ≤ 1 := by
  rw [← map_intCast (algebraMap ℚ (w.adicCompletion ℚ)), valued_algebraMap]
  have := w.valuation_le_one (K := ℚ) z
  simpa using this

theorem exists_int_add_prime_mul (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) (a : AfP p) (ha : IsIntAf a) :
    ∃ (z : ℤ) (a' : AfP p), IsIntAf a' ∧ a = (z : AfP p) + (l : AfP p) * a' := by
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hl).irreducible
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  let w0 : HeightOneSpectrum ℤ := ⟨Ideal.span {(l : ℤ)}, hmax.isPrime, by simpa using hl0⟩
  have hw0 : w0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    have hp : (p : ℤ) ∈ Ideal.span {(l : ℤ)} := by
      change (p : ℤ) ∈ w0.asIdeal; rw [h]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at hp
    have hd : l ∣ p := by exact_mod_cast hp
    rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) l hd) with h1 | h1
    · exact hl.ne_one h1
    · exact hlp h1
  let v0 : AwayP p := ⟨w0, hw0⟩
  have hlq0 : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hlv : ∀ w : HeightOneSpectrum ℤ, w.valuation ℚ (l : ℚ) ≤ 1 := fun w => by
    have := w.valuation_le_one (K := ℚ) (l : ℤ); simpa using this
  obtain ⟨z, hz⟩ := exists_int_valued_sub_le w0 (ha v0) hlq0 (hlv w0)
  refine ⟨z, (a - (z : AfP p)) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹, ?_, ?_⟩
  · intro v
    rw [mem_adicCompletionIntegers, map_mul, map_sub, map_intCast, AlgHom.commutes, Valuation.map_mul,
      valued_algebraMap, map_inv₀]
    have hne : v.1.valuation ℚ (l : ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 hlq0
    by_cases hv : v = v0
    · subst hv
      rw [mul_inv_le_iff₀ (zero_lt_iff.2 hne), _root_.one_mul]
      exact hz
    · have hnot : (l : ℤ) ∉ v.1.asIdeal := by
        intro hm
        apply hv
        have hle : Ideal.span {(l : ℤ)} ≤ v.1.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hm
        have heq := hmax.eq_of_le v.1.isPrime.ne_top hle
        exact Subtype.ext (HeightOneSpectrum.ext heq.symm)
      have h1 : v.1.valuation ℚ (l : ℚ) = 1 := by
        have := (valuation_eq_one_iff_notMem (v := v.1) (K := ℚ) (r := (l : ℤ))).2 hnot
        simpa using this
      rw [h1, inv_one, _root_.mul_one]
      exact (Valuation.map_sub _ _ _).trans (max_le (ha v) (valued_intCast v.1 z))
  · have e : (l : AfP p) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹ = 1 := by
      rw [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, mul_inv_cancel₀ hlq0, map_one]
    calc a = (z : AfP p) + (a - (z : AfP p)) * ((l : AfP p) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹) := by
          rw [e, _root_.mul_one]; ring
      _ = _ := by ring

theorem exists_int_add_mul (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (a : AfP p) (ha : IsIntAf a) :
    ∃ (z : ℤ) (a' : AfP p), IsIntAf a' ∧ a = (z : AfP p) + (n : AfP p) * a' := by
  induction n using Nat.recOnMul generalizing a with
  | zero => exact absurd hn (lt_irrefl 0)
  | one => exact ⟨0, a, ha, by simp⟩
  | prime l hl =>
    exact exists_int_add_prime_mul l hl (fun h => by
      subst h; exact hl.ne_one ((Nat.coprime_self _).1 hnp)) a ha
  | mul m k ihm ihk =>
    have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
    have hk : 0 < k := Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
    obtain ⟨hmp, hkp⟩ := Nat.coprime_mul_iff_left.1 hnp
    obtain ⟨z1, a1, h1, e1⟩ := ihm hm hmp a ha
    obtain ⟨z2, a2, h2, e2⟩ := ihk hk hkp a1 h1
    exact ⟨z1 + m * z2, a2, h2, by rw [e1, e2]; push_cast; ring⟩

end GlobalTheory.LKGeo.LaHatMod

namespace GlobalTheory.LKGeo

theorem exists_inAf_add_nsmul_of_mem_laHat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ), 0 < n → n.Coprime p →
    ∀ v ∈ LaHat D, ∃ (x : D.La) (w : TensorProduct ℚ (AfP p) (VQ D)), w ∈ LaHat D ∧ v = inAf D x + n • w := by
  intro p _ D n hn hnp v hv
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a, x, ha, rfl⟩ := hu
    obtain ⟨z, a', ha', e⟩ := LaHatMod.exists_int_add_mul n hn hnp a ha
    refine ⟨z • x, a' ⊗ₜ ((1 : ℚ) ⊗ₜ x), AddSubgroup.subset_closure ⟨a', x, ha', rfl⟩, ?_⟩
    have h1 : ((z : AfP p)) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = (1 : AfP p) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] (z • x)) := by
      rw [show (z : AfP p) = (z : ℚ) • (1 : AfP p) by rw [← Algebra.algebraMap_eq_smul_one, map_intCast],
        TensorProduct.smul_tmul, TensorProduct.smul_tmul',
        show (z : ℚ) • (1 : ℚ) = z • (1 : ℚ) by simp, TensorProduct.smul_tmul]
    have h2 : ((n : AfP p) * a') ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = n • (a' ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x)) := by
      rw [← nsmul_eq_mul, TensorProduct.smul_tmul']
    rw [e, TensorProduct.add_tmul, h1, h2, inAf]
  | zero => exact ⟨0, 0, zero_mem _, by simp [inAf]⟩
  | add u u' _ _ ih ih' =>
    obtain ⟨x, w, hw, e⟩ := ih
    obtain ⟨x', w', hw', e'⟩ := ih'
    refine ⟨x + x', w + w', add_mem hw hw', ?_⟩
    rw [e, e', inAf, inAf, inAf, TensorProduct.tmul_add, TensorProduct.tmul_add, smul_add]
    abel
  | neg u _ ih =>
    obtain ⟨x, w, hw, e⟩ := ih
    refine ⟨-x, -w, neg_mem hw, ?_⟩
    rw [e, inAf, inAf, TensorProduct.tmul_neg, TensorProduct.tmul_neg, smul_neg, neg_add]

end GlobalTheory.LKGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntersectionAtPlace
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BigOn.Exp.SerBase
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

section BaseChange

variable {E K₀ K ι : Type} [Field E] [NumberField E] [Field K₀] [NumberField K₀] [Field K] [NumberField K] [Fintype ι]
  {n : ℕ}

theorem map_mem_nabAtr_comp (f : K₀ →+* K) (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.IsLattice E M) {x : VV K₀ lam} (hx : x ∈ nabAtr emb lam M) :
    (⟨MvPolynomial.map f x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam _ x.2⟩ : VV K lam) ∈
      nabAtr (fun τ => f.comp (emb τ)) lam M := by
  classical
  unfold nabAtr nabK at hx ⊢
  rw [Submodule.mem_comap] at hx ⊢
  change MvPolynomial.map f x.1 ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)
  change x.1 ∈ nabP lam (fun τ => dualFr (tauLat emb τ M)) at hx
  refine GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => ?_
  obtain ⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀),
      ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by
    refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩
    have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))
  have hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal :=
    fun t ht h => ht ((hw₀ t).2 h)
  obtain ⟨hLoc, -, -⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hT : ∀ τ, Submodule.IsLattice K₀ (tauLat emb τ M) := fun τ => tauLatLattice E K₀ ι n emb τ M hM
  choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀
  let B₀ : ι → GL (Fin n) K₀ := fun τ => inside₂ K₀ n (C τ)
  have hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ)) := fun τ =>
    GlobalTheory.NabBC.isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)
  have L1 := (hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1
  have L0 := (hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1
  have hx0 : x.1 ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M)) :=
    GlobalTheory.NabBC.mem_localization_of_mem' _ hx
  rw [L0] at hx0
  obtain ⟨g, ⟨s, hs, hsg⟩, hg⟩ := hx0
  rw [L1]
  refine ⟨MvPolynomial.map f g, ⟨RingOfIntegers.mapRingHom f s, hw s hs, ?_⟩, ?_⟩
  · refine (congrArg (· ∈ nabStd K lam) (GlobalTheory.NabBC.map_smul_int f s g)).mpr ?_
    have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1
    have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
    have h3 : MvPolynomial.map f (s • g) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))) :=
      Submodule.subset_span ⟨_, hsg, rfl⟩
    rw [h1, ← h2] at h3
    have h4 : (MvPolynomial.map (RingHom.id K) '' (nabStd K lam : Set (Pol K ι n))) = (nabStd K lam : Set (Pol K ι n)) := by
      ext y
      simp [MvPolynomial.map_id]
    rw [h4, Submodule.span_eq] at h3
    exact h3
  · change actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) = MvPolynomial.map f x.1
    rw [← GlobalTheory.ValCmp.use₂]
    exact congrArg (MvPolynomial.map f) hg

end BaseChange

end GlobalTheory.BigOn.Exp.SerBase

namespace GlobalTheory.BigOn.Exp.SerBase

theorem latIoAt : LatIoAt := by
  refine AtTw.of_forall fun Fm x hx i p hR hM w hw j => ?_
  intro ρ hρ hpin c hc hs
  obtain ⟨gramR, c0R, c0L, hft, u, hu, hsc⟩ := hs
  refine ⟨u, hu, fun h hh P hP => ?_⟩
  have hL := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hio : IoExt (R2 p) := hR.ioExt
  have hB := hρ.base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have hlam := hBo.lam
  have hMlat := GlobalTheory.LatFull.latAt_isLattice _ ρ hρ ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h
  obtain ⟨hPh, hPF⟩ := (mem_harmLat _ _ _).1 hP
  rw [hlam] at hPF
  have key : ∀ φ ∈ coefLatFn (embLL0 (Fm.D x i)) (labLL0 (Fm.D x i)) (smallInt (Fm.D x i)) (lamV (Fm.D x i) j)
      ((ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).latAt (finPt (Vc (Fm.D x i) j) h)),
      ∃ F : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j), F ∈ nabAtr (labLL (Fm.D x i)) (lamV (Fm.D x i) j)
        ((ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).latAt (finPt (Vc (Fm.D x i) j) h)) ∧
        φ = coefFn (Fm.D x i).what₂.embLL (lamV (Fm.D x i) j) (F : Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨F₀, hF₀, rfl⟩ := hφ
      refine ⟨⟨MvPolynomial.map (Fm.D x i).LL0.val.toRingHom F₀.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ F₀.2⟩,
        map_mem_nabAtr_comp (Fm.D x i).LL0.val.toRingHom (labLL0 (Fm.D x i)) _ _ hMlat hF₀, ?_⟩
      funext y
      rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom]
      rfl
    | zero => exact ⟨0, zero_mem _, funext fun y => by simp [coefFn]⟩
    | add φ ψ _ _ h1 h2 =>
      obtain ⟨F1, m1, rfl⟩ := h1
      obtain ⟨F2, m2, rfl⟩ := h2
      exact ⟨F1 + F2, add_mem m1 m2, funext fun y => by simp [coefFn, mul_add]⟩
    | smul a φ _ h1 =>
      obtain ⟨F1, m1, rfl⟩ := h1
      obtain ⟨t, ht⟩ := a.2
      refine ⟨RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t • F1, Submodule.smul_mem _ _ m1, funext fun y => ?_⟩
      have e1 : ((RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t • F1 : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j)) :
          Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) =
          MvPolynomial.C (((RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t : 𝓞 (Fm.D x i).what₂.LL)) :
            (Fm.D x i).what₂.LL) * (F1 : Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) := by
        rw [← MvPolynomial.smul_eq_C_mul]
        rfl
      have e2 : (Fm.D x i).what₂.embLL (((RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t : 𝓞 (Fm.D x i).what₂.LL)) :
          (Fm.D x i).what₂.LL) = (a : ℂ) := by
        rw [← ht]
        rfl
      show (a : ℂ) * coefFn _ _ (F1 : Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) y = _
      rw [e1, coefFn, coefFn, map_mul, MvPolynomial.eval₂Hom_C, e2]
      ring
  obtain ⟨F, hF, hFe⟩ := key _ hPF
  have hM' : (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).latAt (finPt (Vc (Fm.D x i) j) h) =
      Bridge.hLat (Vc (Fm.D x i) j) (fin (Vc (Fm.D x i) j) h) :=
    GlobalTheory.LatAtHLat.latAt_eq_hLat _ _ _ _ (GlobalTheory.LatFull.baseFrame_one_eq _ _ _ (hρ.latS _ j _)) _
  refine ⟨c0L j F, ⟨gramR, c0R, c0L, hft, F, by rw [← hM']; exact hF, rfl⟩, ?_⟩
  obtain ⟨u', w₀, hu', -, hw₀⟩ := IsChosenExtremalVector.io _ ((fw2 p).hv₀ j _) hio
  have huu : u' = (u : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ) :=
    funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  rw [huu] at hw₀
  have hm : ∀ τ, (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).w.p τ +
      (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).w.q τ ≤ (Wc (Fm.D x i) j).rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE (Fm.D x i) τ)
    rw [← h1] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function _ _ _ _ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).F.BS hB.wt hm
  exact IsScaleAt.ioP_eq (Rl := p.R) hsc hinj hPh
    (GlobalTheory.SeriesTie.UnivRat.ioP_mem_harmonic hC.lev hC.thP (hC.models.cV j) hB (hpin.psi _ j _) (hpin.inf _ j _)
      (hpin.cartT _ j _) (hpin.onbS _ j _) (hpin.onbT _ j _) (hpin.mu0 _ j _) (hpin.eta _ j _) (hpin.ap _ j _) (hpin.am _ j _)
      _ w₀ hw₀ _) hFe

end GlobalTheory.BigOn.Exp.SerBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorBundlePullback
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LatDiv

variable {p : ℕ} [Fact p.Prime]

def intAf (p : ℕ) : AddSubgroup (AfP p) where
  carrier := {a | IsIntAf a}
  zero_mem' := fun v => by simp
  add_mem' := fun ha hb v => by rw [map_add]; exact add_mem (ha v) (hb v)
  neg_mem' := fun ha v => by rw [map_neg]; exact neg_mem (ha v)

def extF (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) : AfP p ⊗[ℚ] VQ D →ₗ[AfP p] AfP p :=
  LinearMap.liftBaseChange (AfP p)
    ((Algebra.linearMap ℚ (AfP p)) ∘ₗ LinearMap.liftBaseChange ℚ ((Algebra.linearMap ℤ ℚ) ∘ₗ f))

theorem extF_tmul (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) (a : AfP p) (x : D.La) :
    extF D f (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = a * ((f x : ℤ) : AfP p) := by
  simp [extF, LinearMap.liftBaseChange_tmul, Algebra.smul_def]

theorem extF_mem (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) {w : AfP p ⊗[ℚ] VQ D} (hw : w ∈ LaHat D) :
    extF D f w ∈ intAf p := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    intro v
    rw [extF_tmul, map_mul, map_intCast]
    exact mul_mem (ha v) (intCast_mem _ _)
  | zero => simpa using (intAf p).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem int_dvd (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) (x : D.La) (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p)
    (w : AfP p ⊗[ℚ] VQ D) (hw : w ∈ LaHat D) (h : inAf D x = n • w) : (n : ℤ) ∣ f x := by
  have hb := extF_mem D f hw
  have e : ((f x : ℤ) : AfP p) = (n : AfP p) * extF D f w := by
    have := congrArg (extF D f) h
    rw [inAf, extF_tmul, _root_.one_mul, _root_.map_nsmul, nsmul_eq_mul] at this
    exact this
  set q : ℚ := (f x : ℚ) / n with hq
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hval : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, v.valuation ℚ q ≤ 1 := by
    intro v
    by_cases hv : v.asIdeal = Ideal.span {(p : ℤ)}
    · have h1 : v.valuation ℚ (n : ℚ) = 1 := by
        have : (n : ℚ) = algebraMap ℤ ℚ (n : ℤ) := by simp
        rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff, hv, Ideal.mem_span_singleton]
        intro hd
        have : (p : ℤ) ∣ (n : ℤ) := hd
        have h2 : p ∣ n := by exact_mod_cast this
        have h3 : p ∣ Nat.gcd n p := Nat.dvd_gcd h2 dvd_rfl
        rw [hnp] at h3
        exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)
      have h2 : v.valuation ℚ ((f x : ℤ) : ℚ) ≤ 1 := by
        rw [← eq_intCast (algebraMap ℤ ℚ), IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact v.intValuation_le_one _
      rw [hq, map_div₀, h1, div_one]; exact h2
    · let v' : AwayP p := ⟨v, hv⟩
      have hbv := hb v'
      have e2 := congrArg (AfP.eval v') e
      rw [map_intCast, map_mul, map_natCast] at e2
      have hqv : algebraMap ℚ (v.adicCompletion ℚ) q = AfP.eval v' (extF D f w) := by
        have hn' : algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ) ≠ 0 := (map_ne_zero _).2 hn0
        have : algebraMap ℚ (v.adicCompletion ℚ) q * algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ) =
            ((f x : ℤ) : v.adicCompletion ℚ) := by
          rw [← map_mul, hq, div_mul_cancel₀ _ hn0, map_intCast]
        rw [← mul_left_inj' hn', this, e2, map_natCast]
        ring
      have hc : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q :=
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q
      rw [← hc, hqv]
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hbv
  obtain ⟨k, hk⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q hval
  refine ⟨k, ?_⟩
  have : ((k : ℤ) : ℚ) = (f x : ℚ) / n := by rw [← eq_intCast (algebraMap ℤ ℚ)]; exact hk.trans hq
  have h4 : ((f x : ℤ) : ℚ) = ((n : ℤ) * k : ℤ) := by
    push_cast; rw [this]; field_simp
  exact_mod_cast h4

end GlobalTheory.LKGeo.LatDiv

namespace GlobalTheory.LKGeo.LatDiv

theorem eq_nsmul_of_inAf_eq_nsmul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (x : D.La) (n : ℕ), 0 < n → n.Coprime p →
    ∀ w ∈ LaHat D, inAf D x = n • w → ∃ z, x = n • z := by
  intro p _ D x n hn hnp w hw h
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hd : ∀ i, (n : ℤ) ∣ b.coord i x := fun i => int_dvd D (b.coord i) x n hn hnp w hw h
  choose c hc using hd
  refine ⟨∑ i, c i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr x]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : b.repr x i = (n : ℤ) * c i := hc i
  rw [this, mul_smul]
  exact Nat.cast_smul_eq_nsmul ℤ n _

end GlobalTheory.LKGeo.LatDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismRepresentation
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_automorphism_representation : Hypotheses2 → Gram → DeepGood → Covers fun Fm x _ ι p i Y _ _ => ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* (LevelAut (dat p i) Y.d.l₂)) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ Pb.comap π = grpHR fr ∧ (∀ k, (H k).comap π = grpGHR fr k) ∧ (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (Fm.D x ι).ntypes.e0) : Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) := by
  intro _ _ _
  refine GlobalTheory.CovTop.CovSz.covers_of_lifts (GlobalTheory.CovTop.Sizes.hostN 0) ?_
  intro eps Fm x hx ι p i C _ hN _ Y hY
  exact GlobalTheory.CovTop.BadRep.badRep_at p i Y hY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndicatorReadsNormPowerUnitVectorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_indicator_reads_norm_power_unit_vector : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
    D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsStdLat LS → IsStdLat LT → IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    IsSBHalf (cA D e) (latO S T LS LT fun _ => True) (cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T)) →
    ∀ (κ : ℂ) (e0 : VC D a d → ℂ) (vac : WO S T → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
    Reads ψ θ hS hT ⊤ δ 1 (κ • e0) vac → IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac →
    ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm →
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads ψ θ hS hT ⊤ δ 1
      ((κ * ζ) • ((Real.sqrt ((Ideal.absNorm (D.host.conj • modul P c) : ℝ) ^ (a * d)) : ℂ))⁻¹ •
        Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • modul P c) d)) e0)
      (Tm (cosetFn (cA D e) (D.host.conj • modul P c) 0)) := by
  first | exact @GlobalTheory.SkewLevel.reads_level | exact GlobalTheory.SkewLevel.reads_level | (intros; apply GlobalTheory.SkewLevel.reads_level <;> assumption)
end

