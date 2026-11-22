import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStableRationalLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Formalism.DoubleCosetMeasures.LatticeCoset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0346
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GalAlgClosureExistsPosPowApplyEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem galAlgClosure_exists_pos_pow_apply_eq :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (σ : G E Ω) (t : Ω), ∃ k : ℕ, 0 < k ∧ (σ ^ k) t = t := by
  intro E Ω _ _ _ _ _ σ t
  have hint : IsIntegral E t :=
    ((IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic t).isIntegral
  have hmem : ∀ i : ℕ, (σ ^ i) t ∈ (minpoly E t).rootSet Ω := by
    intro i
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    have h := Polynomial.aeval_algHom_apply ((σ ^ i : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) t (minpoly E t)
    rw [minpoly.aeval, map_zero] at h
    exact h
  haveI : Finite ((minpoly E t).rootSet Ω) := ((minpoly E t).rootSet_finite Ω).to_subtype
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun i : ℕ => (⟨(σ ^ i) t, hmem i⟩ : (minpoly E t).rootSet Ω))
  have heq' : (σ ^ i) t = (σ ^ j) t := congrArg Subtype.val heq
  have key : ∀ a b : ℕ, a < b → (σ ^ a) t = (σ ^ b) t → ∃ k : ℕ, 0 < k ∧ (σ ^ k) t = t := by
    intro a b hab h
    refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
    apply (σ ^ a).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
    exact h.symm
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h heq'
  · exact key j i h heq'.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyLocalGlobal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SysFin

open GlobalTheory.CoefDuty

section Places
variable {R : Ranks} {H : Host R}

theorem intCast_mem_conj {v w : PlE H} (h : IsConjPl H v w) (n : ℤ) :
    (n : 𝓞 H.E) ∈ v.asIdeal ↔ (n : 𝓞 H.E) ∈ w.asIdeal :=
  h _ _ (by simp [map_intCast])

theorem intCast_mem_over {w : PlE H} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield H.E))}
    (h : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield H.E)) (𝓞 H.E)) = v.asIdeal) (n : ℤ) :
    (n : 𝓞 H.E) ∈ w.asIdeal ↔ (n : 𝓞 (maximalRealSubfield H.E)) ∈ v.asIdeal := by
  rw [← h, Ideal.mem_comap, map_intCast]

end Places

theorem finite_intCast_mem {K : Type} [Field K] [NumberField K] (N : ℤ) (hN : N ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | (N : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(N : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem exists_intCast_mem {K : Type} [Field K] [NumberField K] (q : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : 𝓞 K) ∈ q.asIdeal := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot q.ne_bot
  have h := Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral (R := ℤ) x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine ⟨n, hn0, ?_⟩
  rw [Ideal.mem_comap, eq_intCast] at hn
  exact hn

theorem intCast_mem_of_dvd {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {n N : ℤ} (hd : n ∣ N)
    (h : (n : 𝓞 K) ∈ v.asIdeal) : (N : 𝓞 K) ∈ v.asIdeal := by
  obtain ⟨b, rfl⟩ := hd
  push_cast
  exact Ideal.mul_mem_right _ _ h

section Eig
variable {D : D7}

theorem genAt_mono {l : ℕ} {Q Q' : Finset (PlE D.host)} (hQ : Q ⊆ Q') {v : PlE D.host} {k : ℕ}
    (h : GenAt D l Q' v k) : GenAt D l Q v k :=
  ⟨h.1, h.2.1, h.2.2.1, fun hv => h.2.2.2.1 (hQ hv), h.2.2.2.2⟩

open Classical in
theorem eigSet_restrict {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) (l : ℕ) {Q Q' : Finset (PlE D.host)} (hQ : Q ⊆ Q')
    {c : PlE D.host → ℕ → ℂ} (hc : c ∈ EigSet X l Q) :
    (fun v k => if GenAt D l Q' v k then c v k else 0) ∈ EigSet X l Q' := by
  obtain ⟨-, y, hy, hy'⟩ := hc
  refine ⟨fun v k hg => if_neg hg, y, hy, fun v k s ϖ hg hcj hu => ?_⟩
  simp only [if_pos hg]
  exact hy' v k s ϖ (genAt_mono hQ hg) hcj hu

theorem eigSet_transport (M : MtFam D) {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ = μ') (hj : j = j')
    (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m) (l : ℕ) (Q : Finset (PlE D.host))
    (c : PlE D.host → ℕ → ℂ) : c ∈ EigSet (M μ j a1 a2) l Q → c ∈ EigSet (M μ' j' b1 b2) l Q := by
  subst hμ hj; exact id

end Eig

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
open Classical in

theorem ptSys_finite : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ w : D.what₂.places.Pl, ∃ (F : Finset (PlE D.host)) (Sy : Finset (PlE D.host → ℕ → ℂ)), ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), AutSpec A M tp.tup Sp.iq L.Y L.C → ∀ (i : (withLoc L).nd.Loc) (x : (withLoc L).nd.X i), (withLoc L).nd.w i = w → ∃ c ∈ Sy, ∀ v, v ∉ F → ∀ k, GlobalTheory.CoefDuty.ptSys (withLoc L) i x v k = c v k := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb w
  by_cases hw0 : D.what₂.muAt w = D.what₂.mu0
  · refine ⟨∅, ∅, fun big L Sp Au i x hi => absurd hw0 ?_⟩
    have := L.X.w_tw i
    rw [show L.X.w i = w from hi] at this
    exact this
  choose nq hnq0 hnqm using fun q : PlE D.host => exists_intCast_mem q
  set N : ℤ := (D.host.g 0 : ℤ) * (D.host.g 1 : ℤ) * (D.host.pde : ℤ) * (D.host.pde' : ℤ) * ∏ q ∈ C.Q w, nq q with hNdef
  have hN : N ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
    · exact_mod_cast (D.host.g_prime 0).ne_zero
    · exact_mod_cast (D.host.g_prime 1).ne_zero
    · exact_mod_cast D.host.pde_prime.ne_zero
    · exact_mod_cast D.host.pde'_prime.ne_zero
    · exact Finset.prod_ne_zero_iff.2 fun q _ => hnq0 q
  have hfinN := finite_intCast_mem (K := D.host.E) N hN
  set F : Finset (PlE D.host) := hfinN.toFinset with hFdef
  have hF : ∀ v : PlE D.host, v ∉ F → (N : 𝓞 D.host.E) ∉ v.asIdeal := fun v hv h => hv (hfinN.mem_toFinset.2 h)
  set l := D.what₂.places.resChar w with hldef
  set Q' : Finset (PlE D.host) := C.Q w ∪ F with hQ'

  have hB : ∀ (j : Fin D.R.m) v k (s : SplitPlace D.host.E), GenAt D l Q' v k → IsConjPl D.host v s.w →
      s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w) j) := by
    intro j v k s hg hc hs
    have hvF : v ∉ F := fun h => hg.2.2.2.1 (Finset.mem_union_right _ h)
    have key : ∀ (w' : PlE D.host) (n : ℤ), NG.OverPl w' s.v → n ∣ N → (n : 𝓞 D.host.E) ∉ w'.asIdeal := by
      intro w' n hov hd hn
      apply hF v hvF
      apply intCast_mem_of_dvd hd
      rw [intCast_mem_conj hc, intCast_mem_over s.w_under]
      exact (intCast_mem_over hov n).1 hn
    rcases hs with ⟨w', hov, k0, hk0⟩ | hq
    · refine key w' (D.host.g k0) hov ?_ (by exact_mod_cast hk0)
      fin_cases k0
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) _
    · obtain ⟨w', hov, hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp w hw0 j hq
      rcases hw' with hQ | hp
      · exact key w' (nq w') hov (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hQ) _) (hnqm w')
      · split_ifs at hp
        · exact key w' D.host.pde' hov (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) (by exact_mod_cast hp)
        · exact key w' D.host.pde hov (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) (by exact_mod_cast hp)
  have hfin : ∀ j : Fin D.R.m, (EigSet (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)) l Q').Finite := fun j =>
    GlobalTheory.T.heckeEigenvalueSystemSet_finite GlobalTheory.T.heckeDoubleCosetOperators_standardFacts D _ _ _ l Q' _ (hMt.hyp w j) (hB j)
  refine ⟨F, Finset.univ.biUnion fun j : Fin D.R.m => (hfin j).toFinset, fun big L Sp Au i x hi => ?_⟩
  obtain ⟨Hk, -⟩ := GlobalTheory.FitHecke.heckeOpen_withLoc D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L Sp Au
  have hpt := GlobalTheory.T.localisationPointEigenSystem_mem (withLoc L) (mtL L M) Hk.av i x
  have hwi : L.X.w i = w := hi
  have hl : L.X.l i = l := by rw [← L.X.w_l i, hwi]
  have hmem := GlobalTheory.FitHecke.mem_locs_self (D := withLoc L) i
  have hQ : L.X.Q i = C.Q w := by rw [← hwi]; exact (Sp.Q_eq _ _ i hmem).trans (Sp.Qc_eq _ _)
  have hj := L.X.j_range i
  let jf : Fin D.R.m := ⟨L.X.j i - 1, by omega⟩
  have hpt' : ptSys (withLoc L) i x ∈ EigSet (M (L.X.mu i) (L.X.j i) hj.1 hj.2) l (C.Q w) := by
    rw [← hl, ← hQ]; exact hpt
  have hpt'' := eigSet_transport M ((L.X.mu_w i).trans (by rw [hwi])) (show L.X.j i = jf.1 + 1 by simp [jf]; omega)
    hj.1 hj.2 (by omega) (by omega) l (C.Q w) _ hpt'
  refine ⟨fun v k => if GenAt D l Q' v k then ptSys (withLoc L) i x v k else 0, ?_, ?_⟩
  · refine Finset.mem_biUnion.2 ⟨jf, Finset.mem_univ _, (hfin jf).mem_toFinset.2 ?_⟩
    exact eigSet_restrict _ l Finset.subset_union_left hpt''
  · intro v hv k
    show _ = if GenAt D l Q' v k then _ else _
    split_ifs with hg
    · rfl
    · unfold ptSys
      rw [if_neg]
      intro hg'
      apply hg
      have hg2 : GenAt D l (C.Q w) v k := by rw [← hl, ← hQ]; exact hg'
      exact ⟨hg2.1, hg2.2.1, hg2.2.2.1, fun h => (Finset.mem_union.1 h).elim hg2.2.2.2.1 hv, hg2.2.2.2.2⟩

end GlobalTheory.SysFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapHypOfNodes
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top

namespace GlobalTheory.Mem.Top.NodeGap

theorem gapHyp_of_nodes (D : D7) (hm : 1801 ≤ D.R.m) (h : ℕ) (hh : 16 * (D.R.r : ℝ) ^ 19 ≤ (h : ℝ))
    (hb : ∀ τ, ∃ b1 : ℤ, ∀ j : Fin D.R.m, (D.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ)) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D := by
  refine ⟨?_, ?_⟩
  · have h1 := D.R.m_add_three_le_k
    show 1801 ≤ D.R.k + D.R.m - 1
    omega
  · intro τ j hj
    obtain ⟨b1, hb1⟩ := hb τ
    rw [hb1 ⟨j.1 + 1, hj⟩, hb1 j]
    have h2 : 16 * D.R.r ^ 19 ≤ h := by exact_mod_cast hh
    have h3 : (16 * (D.R.r : ℚ) ^ 19) ≤ (h : ℚ) := by exact_mod_cast h2
    push_cast
    linarith

private theorem ev_mono_of_forall_imp {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  unfold Ev at hp ⊢
  obtain ⟨w, hw, H⟩ := hp
  refine ⟨w, hw, fun eps C8 a b c d => ?_⟩
  obtain ⟨K0, H1⟩ := H eps C8 a b c d
  refine ⟨K0, fun C e f g => ?_⟩
  obtain ⟨c1, H2⟩ := H1 C e f g
  refine ⟨c1, fun cD hc => ?_⟩
  obtain ⟨c2, H3⟩ := H2 cD hc
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H4⟩ := H3 ch hch
  exact ⟨x0, fun K k1 k2 k3 k4 k5 => h K (H4 K k1 k2 k3 k4 k5)⟩

theorem ev_gapHyp : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → Formalism.L2.SG.ConcreteSettingExists.GapHyp X.toD7 := by
  refine ev_mono_of_forall_imp ?_ (ev_nodes 16 19 1801)
  intro K hK X hX
  obtain ⟨hm, h, hh, hb⟩ := hK X hX
  exact gapHyp_of_nodes X.toD7 hm h hh fun τ => (hb τ).imp fun b1 hb1 j => (hb1 j).1

end GlobalTheory.Mem.Top.NodeGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemFieldStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_finiteIdele_value_mem_field : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (M : IntermediateField ℚ ℂ), valueField χ 0 ≤ M → (∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ x, (∀ w : InfinitePlace E, (x.val : AdeleRing (𝓞 E) E).1 w = 1) → ((χ.1 x : ℂˣ) : ℂ) ∈ M := by
  first | exact @GlobalTheory.HeckeValField.mem_of_inf_eq_one | exact GlobalTheory.HeckeValField.mem_of_inf_eq_one | (intros; apply GlobalTheory.HeckeValField.mem_of_inf_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeIdempotentProjectorVanishingBaseChangeTwistStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIdempotentProjector_vanishing_baseChange_twistSide : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host),
    1 ≤ j → j ≤ D.R.m → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 →
    phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b = 0 := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.phiKop_eGT_piKop_eq_zero | exact GlobalTheory.HeightCounting.FormsStep.phiKop_eGT_piKop_eq_zero | (intros; apply GlobalTheory.HeightCounting.FormsStep.phiKop_eGT_piKop_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStableRationalLatticeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_stable_rational_lattice : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → HkStab D T S In := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.hkStab_all | exact GlobalTheory.HeightCounting.FormsStep.hkStab_all | (intros; apply GlobalTheory.HeightCounting.FormsStep.hkStab_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualCoefficientSpaceUnique
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF.DDHw

theorem dd_hw_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu → mu = (lam τ₀).w := by
  intro L _ _ _ n ι _ K _ _ emb lam hd τ₀ mu h
  classical
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  obtain ⟨w, hwV, hw0, hB⟩ := GlobalTheory.T.highestWeight_doubleDual_upperTriangular_eigenvector L n ι K emb lam hd τ₀ mu h
  obtain ⟨φ, hφ0, hφV, hφA⟩ := GlobalTheory.T.exists_specialisation_coefficientSpace_to_dualWeyl K n ι lam τ₀ w hwV hw0
  refine GlobalTheory.T.nablaSq_upperEigenvector_weight_eq_highest K n (lam τ₀) mu (φ w) (hφV w hwV) hφ0 fun B hBt => ?_
  have hc0 : detPow K n B (lam τ₀).detShift ≠ 0 := by
    rw [detPow]; exact Units.ne_zero _
  rw [sqAct, ← hφA, hB B hBt, map_smul, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end GlobalTheory.AlgWtF.DDHw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalAtCompletionIntegersChosenUniformiser
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.HD

private theorem lt_one_iff_le_exp_neg_one (g : WithZero (Multiplicative ℤ)) :
    g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  induction g using WithZero.expRecOn with
  | zero => simp
  | exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

theorem isLocalAt_adicCompletionIntegers_uniformizer (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) :
    IsLocalAt (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) := by
  have hv : Valued.v ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)
      = WithZero.exp (-1 : ℤ) := unif_spec P
  have hne : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ≠ 0 := Units.ne_zero _
  have mem : ∀ x : P.adicCompletion L, x ∈ OP P ↔ Valued.v x ≤ 1 := fun x =>
    HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 L) (K := L) (v := P)
  have hexp : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-1 : ℤ) :=
    zero_lt_iff.2 WithZero.exp_ne_zero
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := (mem _).1 h
    rw [map_inv₀, hv, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · intro x hx hnot
    have hx1 : Valued.v x ≤ 1 := (mem x).1 hx
    have hx_eq : Valued.v x = 1 := by
      by_contra hne1
      have hlt : Valued.v x < 1 := lt_of_le_of_ne hx1 hne1
      have hle := (lt_one_iff_le_exp_neg_one _).1 hlt
      refine hnot (((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)⁻¹ * x) ?_ ?_
      · rw [mem, map_mul, map_inv₀, hv]
        exact inv_mul_le_one_of_le₀ hle hexp.le
      · rw [mul_inv_cancel_left₀ hne]
    rw [mem, map_inv₀, hx_eq, inv_one]

end GlobalTheory.Mem.HD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFact
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem Dec_valuation_apply_eq :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (σ : G E Ω), σ ∈ Dec (F := E) A → ∀ t : Ω, A.valuation (σ t) = A.valuation t := by
  first
  | exact @_root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq
  | exact _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq
  | (apply _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevExOfOver
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD

private theorem levEx_of_levelPrimes_eq (D : D7) (S : Finset ℕ) (g : Fin 2 → ℕ) (a b c : ℕ) (hS : S = {g 0, g 1, a, b, c})
    (hlev : ∀ p, p ∈ D.host.levelPrimes ↔ p ∈ S ∨ ∃ u, p = (D.mem u).A.T)
    (hg : ∀ i, D.host.g i = g i) (ha : D.host.pde = a) (hb : D.host.pde' = b) (hc : q0Av D = c) : LevEx D := by
  intro p
  rw [hlev, hS]
  simp only [Finset.mem_insert, Finset.mem_singleton, hg, ha, hb, hc, Fin.exists_fin_two]
  tauto

theorem levEx_of_over : ∀ (D : D7) (P : PreCh) (Lv : LevCh P), Over D P Lv →
    P.H.levelPrimes = {P.H.g 0, P.H.g 1, P.H.pde, P.H.pde', DC.q0H P.H} → LevEx D ∧ ∀ N h, LevEx (setDiv D N h) := by
  intro D P Lv hO hlev
  obtain ⟨sp, hT, hY, hA, hV, hz, X, hX, rfl⟩ := hO
  refine (fun hD => ⟨hD, fun _ _ => hD⟩) ?_
  obtain ⟨B, C, W, V, S, Ns, G⟩ := X
  cases B
  dsimp only at hX
  subst hX
  refine levEx_of_levelPrimes_eq _ P.H.levelPrimes P.H.g P.H.pde P.H.pde' (DC.q0H P.H) hlev ?_ (fun _ => rfl) rfl rfl ?_
  · intro p
    have hT' := C.A_T
    show p ∈ P.H.levelPrimes ∪ Finset.univ.image Lv.T ↔ _
    rw [Finset.mem_union, Finset.mem_image]
    exact or_congr Iff.rfl
      ⟨fun ⟨u, _, hu⟩ => ⟨u, hu.symm.trans (hT' u).symm⟩, fun ⟨u, hu⟩ => ⟨u, Finset.mem_univ _, (hT' u).symm.trans hu.symm⟩⟩
  · unfold q0Av DC.q0H rPrAv DC.rPrH LevelStarExponents.condE
    rfl

end GlobalTheory.Mem.HD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTiedOfLevEx
section
open Formalism.BasicNotions GlobalTheory.Mem.HD

theorem GlobalTheory.Mem.HD.levelTied_of_levEx : ∀ D : D7, LevEx D → Formalism.L2.Host.LevelTied D :=
  fun D h => ⟨fun p => by
    have hq : Formalism.MainNotions.q0Av D = Formalism.MainNotions.AbsolutelyIrreducibleSpan.q0 D := rfl
    simpa [hq] using h p⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MuZeroCharLocKCongruentRationalInteger
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MuZeroCong

theorem locK_eq_of_sub_mem : ∀ {R : Ranks} {H : Host R} (P : PiBar H) (W : Omg H) (e : ↥(R.Psi) → ℚ) (j : ℕ) (χ : HChar H.E), IsMu0 P W e j χ → ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (u : 𝓞 H.E) (hu : (u : H.E) ≠ 0) (a : ℕ) (ha : a.Coprime (H.g k)), u - (a : 𝓞 H.E) ∈ w.asIdeal → χ.locK w (Units.mk0 (u : H.E) hu) = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹ := by
  intro R H P W e j χ hχ k w hw u hu a ha hua
  have hg : ((H.g k : ℕ) : 𝓞 H.E) ∈ w.asIdeal := by
    have h1 := P.pb_over k
    rw [← hw, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
    exact h1
  have ha_nm : ((a : ℕ) : 𝓞 H.E) ∉ w.asIdeal := by
    intro haw
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have hb := Nat.gcd_eq_gcd_ab a (H.g k)
    rw [Nat.Coprime.gcd_eq_one ha, Nat.cast_one] at hb
    have h1 : (1 : 𝓞 H.E) = ((a : ℕ) : 𝓞 H.E) * ((Nat.gcdA a (H.g k) : ℤ) : 𝓞 H.E)
        + ((H.g k : ℕ) : 𝓞 H.E) * ((Nat.gcdB a (H.g k) : ℤ) : 𝓞 H.E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 H.E) hb
      push_cast at this
      exact this
    rw [h1]
    exact add_mem (Ideal.mul_mem_right _ _ haw) (Ideal.mul_mem_right _ _ hg)
  have hu_nm : u ∉ w.asIdeal := by
    intro huw
    apply ha_nm
    have := Ideal.sub_mem _ huw hua
    simpa using this
  have ha0 : ((a : ℕ) : H.E) ≠ 0 := by
    intro h0
    apply ha_nm
    have : ((a : ℕ) : 𝓞 H.E) = 0 := by
      apply RingOfIntegers.coe_injective
      push_cast
      exact h0
    rw [this]
    exact zero_mem _
  set A : H.Eˣ := Units.mk0 ((a : ℕ) : H.E) ha0 with hA
  set U : H.Eˣ := Units.mk0 (u : H.E) hu with hU
  have hsplit : U = (U * A⁻¹) * A := by group
  have hval : ∀ r : 𝓞 H.E, Valued.v (((r : H.E)) : w.adicCompletion H.E) = w.intValuation r := by
    intro r
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact w.valuation_of_algebraMap r
  have hYval : ((U * A⁻¹ : H.Eˣ) : H.E) = (u : H.E) * ((a : ℕ) : H.E)⁻¹ := by
    simp [hA, hU]
  have hvu : w.intValuation u = 1 := (w.intValuation_eq_one_iff_mem_primeCompl u).mpr hu_nm
  have hva : w.intValuation ((a : ℕ) : 𝓞 H.E) = 1 :=
    (w.intValuation_eq_one_iff_mem_primeCompl _).mpr ha_nm
  have hvd : w.intValuation (u - ((a : ℕ) : 𝓞 H.E)) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [w.intValuation_le_pow_iff_mem, pow_one]
    exact hua
  have hacoe : (((a : ℕ) : 𝓞 H.E) : H.E) = ((a : ℕ) : H.E) := by push_cast; rfl
  have hv' : ∀ x : H.E, Valued.v (algebraMap H.E (w.adicCompletion H.E) x) = w.valuation H.E x :=
    fun x => w.valuedAdicCompletion_eq_valuation' x
  have hY1 : χ.locK w (U * A⁻¹) = 1 := by
    show χ.loc w (atFin w (U * A⁻¹)) = 1
    apply hχ.tame w
    · show Valued.v (algebraMap H.E (w.adicCompletion H.E) ((U * A⁻¹ : H.Eˣ) : H.E)) = 1
      rw [hv', hYval, Valuation.map_mul, Valuation.map_inv, ← hacoe]
      rw [show (u : H.E) = algebraMap (𝓞 H.E) H.E u from rfl,
        show (((a : ℕ) : 𝓞 H.E) : H.E) = algebraMap (𝓞 H.E) H.E ((a : ℕ) : 𝓞 H.E) from rfl,
        w.valuation_of_algebraMap, w.valuation_of_algebraMap, hvu, hva, inv_one, mul_one]
    · show Valued.v (algebraMap H.E (w.adicCompletion H.E) ((U * A⁻¹ : H.Eˣ) : H.E) - 1) ≤ _
      rw [← map_one (algebraMap H.E (w.adicCompletion H.E)), ← map_sub, hv', hYval]
      have hq : (u : H.E) * ((a : ℕ) : H.E)⁻¹ - 1
          = algebraMap (𝓞 H.E) H.E (u - ((a : ℕ) : 𝓞 H.E)) * (algebraMap (𝓞 H.E) H.E ((a : ℕ) : 𝓞 H.E))⁻¹ := by
        rw [map_sub, map_natCast]
        field_simp
      rw [hq, Valuation.map_mul, Valuation.map_inv, w.valuation_of_algebraMap, w.valuation_of_algebraMap, hva,
        inv_one, mul_one]
      exact hvd
  have hAv := hχ.atg k w hw a ha A rfl
  rw [hsplit, map_mul, hY1, one_mul, hAv]

end GlobalTheory.MuZeroCong
end

