import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import GroundTheory.LocalFields.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerfectPairingFiniteModuleRowsCriterion
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun
  GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.CharDual

theorem exists_char_ne_zero (n : ℕ) (hn : n ≠ 0) {G : Type} [AddCommGroup G]
    (hG : ∀ g : G, n • g = 0) {g : G} (hg : g ≠ 0) : ∃ φ : G →+ ZMod n, φ g ≠ 0 := by
  haveI : NeZero n := ⟨hn⟩
  letI : Module (ZMod n) G := AddCommGroup.zmodModule hG
  obtain ⟨f, hf⟩ := GlobalTheory.ZModPerp.exists_dual_ne_zero (n := n) hg
  exact ⟨f.toAddMonoidHom, hf⟩

variable (A : Type) [CommRing A] (n : ℕ)

def charModule : Module A (A →+ ZMod n) where
  smul a φ := φ.comp (AddMonoidHom.mulLeft a)
  one_smul φ := by
    ext b
    show φ (1 * b) = φ b
    rw [one_mul]
  mul_smul a a' φ := by
    ext b
    show φ (a * a' * b) = φ (a' * (a * b))
    rw [mul_left_comm, mul_assoc]
  smul_zero a := by ext b; rfl
  smul_add a φ ψ := by ext b; rfl
  add_smul a a' φ := by
    ext b
    show φ ((a + a') * b) = φ (a * b) + φ (a' * b)
    rw [add_mul, map_add]
  zero_smul φ := by
    ext b
    show φ (0 * b) = 0
    rw [zero_mul, map_zero]

theorem charModule_smul_apply (a : A) (φ : A →+ ZMod n) (b : A) :
    (@HSMul.hSMul A (A →+ ZMod n) (A →+ ZMod n)
      (@instHSMul A (A →+ ZMod n) (charModule A n).toSMul) a φ) b = φ (a * b) := rfl

end GlobalTheory.NewPrime.CharDual

namespace GlobalTheory.NewPrime

open GlobalTheory.NewPrime.CharDual in

theorem charDual_cogenerator : ∀ (A : Type) [CommRing A] [Finite A] (n : ℕ), n ≠ 0 → (n : A) = 0 →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module A Y) (_ : Finite Y) (β : Y →+ A →+ ZMod n),
      Perf A β ∧ ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (v : Fin a → A),
        (∀ x : Fin a → Y, matAct Φ x = 0 → ∑ j, v j • x j = 0) → v ∈ what₂ Φ := by
  intro A _ _ n hn hnA
  haveI : NeZero n := ⟨hn⟩
  letI : Module A (A →+ ZMod n) := charModule A n
  haveI : Finite (A →+ ZMod n) :=
    Finite.of_injective (fun φ : A →+ ZMod n => (φ : A → ZMod n)) DFunLike.coe_injective
  refine ⟨A →+ ZMod n, inferInstance, inferInstance, inferInstance, AddMonoidHom.id _, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a y y'
    rfl
  · intro y hy
    ext b
    exact hy b
  · intro y' hy'
    by_contra h
    obtain ⟨φ, hφ⟩ := exists_char_ne_zero n hn (G := A) (fun g => by
      rw [nsmul_eq_mul, hnA, zero_mul]) h
    exact hφ (hy' φ)
  · intro a Φ v hv
    by_contra hvr
    set Q := (Fin a → A) ⧸ what₂ Φ
    have hQ : ∀ q : Q, n • q = 0 := by
      intro q
      induction q using Submodule.Quotient.induction_on with
      | H w =>
        show n • (Submodule.Quotient.mk w : Q) = 0
        rw [← Nat.cast_smul_eq_nsmul A, ← Submodule.Quotient.mk_smul, hnA, zero_smul,
          Submodule.Quotient.mk_zero]
    have hmk : (Submodule.Quotient.mk v : Q) ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨ψ, hψ⟩ := exists_char_ne_zero n hn hQ hmk
    let L : (Fin a → A) →+ ZMod n := ψ.comp (what₂ Φ).mkQ.toAddMonoidHom
    let x : Fin a → (A →+ ZMod n) := fun j => L.comp (AddMonoidHom.single (fun _ => A) j)
    have key : ∀ (w : Fin a → A) (b : A), (∑ j, w j • x j) b = L (fun k => w k * b) := by
      intro w b
      rw [AddMonoidHom.finset_sum_apply]
      have : (fun k => w k * b) = ∑ j, Pi.single j (w j * b) := (Finset.univ_sum_single _).symm
      rw [this, map_sum]
      rfl
    have hx : matAct Φ x = 0 := by
      funext i
      ext b
      show (∑ j, Φ i j • x j) b = 0
      rw [key]
      have : (fun k => Φ i k * b) = b • Φ i := by
        funext k
        simp [mul_comm]
      rw [this]
      have hmem : b • Φ i ∈ what₂ Φ := Submodule.smul_mem _ b (Submodule.subset_span ⟨i, rfl⟩)
      show ψ (Submodule.Quotient.mk _) = 0
      rw [(Submodule.Quotient.mk_eq_zero _).2 hmem, map_zero]
    have h1 := congrArg (fun f : A →+ ZMod n => f 1) (hv x hx)
    rw [key] at h1
    simp only [mul_one] at h1
    exact hψ h1

end GlobalTheory.NewPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodMatrixRestrictionScalarsBlockDiagonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodMatrix_restrictionScalars_blockDiagonal : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l])
    (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) →
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    ∃ Q₀ : GL (n × Fin r) (Bst P), ∀ g : ↥(GK K),
      (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P)) *
        (Q₀ : Matrix (n × Fin r) (n × Fin r) (Bst P)).map (actSt P (g : GQ l)) = Q₀ := by
  first | exact @GlobalTheory.PMon.period_resScalars | exact GlobalTheory.PMon.period_resScalars | (intros; apply GlobalTheory.PMon.period_resScalars <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariants
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem Fits.invB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) : C.InvB := by
  intro K b hb
  set b' : P.R.B := T.eB.symm b with hb'
  have hfix : ∀ g : ↥(GK K), (P.PD K).actB g b' = b' := by
    intro g
    rw [P.PD_actB]
    apply T.eB.injective
    rw [T.actB, hb', RingEquiv.apply_symm_apply]
    exact hb g g.2
  obtain ⟨c, hc⟩ := (P.PD K).invB b' hfix
  refine ⟨IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c, (inf_le_left : K0 K ≤ K.1) c.2, ?_⟩
  rw [← hF.u]
  have : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c) = b' := hc
  rw [this, hb', RingEquiv.apply_symm_apply]

theorem Fits.invdR {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) : C.InvdR := by
  intro K b hb
  set b' : P.R.BdR := T.eD.symm b with hb'
  have hfix : ∀ g : ↥(GK K), (P.PD K).actdR g b' = b' := by
    intro g
    rw [P.PD_actdR]
    apply T.eD.injective
    rw [T.actD, hb', RingEquiv.apply_symm_apply]
    exact hb g g.2
  obtain ⟨c, hc⟩ := (P.PD K).invdR b' hfix
  refine ⟨(c : Om l), c.2, ?_⟩
  rw [← hF.o]
  have : algebraMap (Om l) P.R.BdR (c : Om l) = b' := hc
  rw [this, hb', RingEquiv.apply_symm_apply]

theorem fits_inv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (C : Core l), Fits T C → C.InvB ∧ C.InvdR :=
  fun _ _ _ _ _ _ hF => ⟨hF.invB, hF.invdR⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlacesOkOfModEqOne
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem placesOk_of_modEq_one : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), q0.Prime → (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p ≡ 1 [MOD H.QS * H.q * H.d]) → (∀ k, q0 ≠ H.g k) → q0 ≠ H.pde → q0 ≠ H.pde' → OverP H q0 w0 → PlacesOk H q0 w0 ∧ 5 ≤ q0 := by
  intro R H q0 w0 hq hmod hg hp hp' hw
  have hprime : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := by
    intro p h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    exacts [H.g_prime 0, H.g_prime 1, H.pde_prime, H.pde'_prime, hq]
  have h4 : (4 : ℕ) ∣ H.QS * H.q * H.d := (by norm_num : 4 ∣ 16).trans H.sixteen_dvd_condN
  have h5 : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], 5 ≤ p := by
    intro p h
    have h1 : p % 4 = 1 % 4 := (hmod p h).of_dvd h4
    have h2 := (hprime p h).two_le
    omega
  refine ⟨⟨hw, ?_, fun p h => ?_⟩, h5 q0 (by simp)⟩
  · have a1 := H.g_ne
    have a2 := H.pde_ne
    have a3 := H.pde_ne_g 0
    have a4 := H.pde_ne_g 1
    have a5 := hg 0
    have a6 := hg 1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true,
      and_true]
    omega
  · have hs := GlobalTheory.Mem.Chr.splitsC_of_modEq_one R H p (hprime p h) (hmod p h)
    have := h5 p h
    refine ⟨hprime p h, by omega, ?_, fun P hP => (GlobalTheory.Mem.Chr.splitsC_main R H p (hprime p h) hs P hP).1⟩
    exact GlobalTheory.SplitEmbSep.not_dvd_discr_of_split (hprime p h) _
      ((GlobalTheory.Mem.Chr.ncard_places_eq_primesOver (hprime p h)).symm.trans hs)

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParameterIsTypeParameterOfTame
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.ParOfPoint

theorem inePol_foldr (D : D7) {w : PlE D.host} (x : D.naut.LP w) {α : Type} (c : α → ℝ) (l : List α)
    (σ : GE D.nd) (hσ : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (l.foldr (fun k acc => D.naut.lpSum (D.naut.lpTw x (c k)) acc) (D.naut.lpZero w)) σ =
      D.naut.inePol x σ ^ l.length := by
  induction l with
  | nil =>
    have h := ((D.naut.unr_iff_ine (D.naut.lpZero w)).1 (D.naut.lpZero_unr w)).2 σ hσ
    rw [D.naut.lpDim_zero, pow_zero] at h
    simpa using h
  | cons k l ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [D.naut.inePol_sum, D.naut.inePol_tw _ _ σ hσ, ih, pow_succ, mul_comm]

theorem inePol_twistIso (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut) (L : List (Part D.naut.CG)) (w : PlE D.host)
    (σ : GE D.nd) (hσ : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaTinv) w) σ =
      D.naut.inePol (isoLoc D.nd D.naut L w) σ := by
  have hd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  have hu : D.naut.inePol (D.naut.locG D.naut.etaTinv w) σ = X - C 1 := by
    have h := ((D.naut.unr_iff_ine _).1 (D.naut.etaTinv_def w).1).2 σ hσ
    rw [hd, pow_one] at h
    rw [h, map_one]
  have hpart : ∀ {a : ℕ} (π : D.naut.CG a),
      D.naut.inePol (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) σ = D.naut.inePol (D.naut.locG π w) σ := by
    intro a π
    rw [D.naut.locG_tw, ((hT w (D.naut.locG π w) (D.naut.locG π w) _ _ 0 hd hd).2.2.2.2.2 σ hσ).2 1 hu,
      Polynomial.scaleRoots_one]
  induction L with
  | nil => rfl
  | cons p L ih =>
    show D.naut.inePol (D.naut.lpSum (spehLoc D.nd D.naut ⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ w)
      (isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaTinv) w)) σ =
      D.naut.inePol (D.naut.lpSum (spehLoc D.nd D.naut p w) (isoLoc D.nd D.naut L w)) σ
    rw [D.naut.inePol_sum, D.naut.inePol_sum, ih]
    unfold spehLoc
    rw [inePol_foldr D _ _ _ σ hσ, inePol_foldr D _ _ _ σ hσ, hpart]

theorem eq_pow_of_mul_eq (A B : ℂ[X]) (n : ℕ) (hA : A.Monic) (hB : B.Monic) (h : A * B = (X - 1) ^ n) :
    A = (X - 1) ^ A.natDegree := by
  have hdvd : A ∣ (X - C 1) ^ n := by rw [map_one, ← h]; exact dvd_mul_right A B
  obtain ⟨j, -, hj⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C (1 : ℂ)) n).1 hdvd
  have e := Polynomial.eq_of_monic_of_associated hA ((monic_X_sub_C (1 : ℂ)).pow j) hj
  rw [e, (monic_X_sub_C (1 : ℂ)).natDegree_pow, natDegree_X_sub_C, mul_one, map_one]

theorem tw_back (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    {a : ℕ} (ha : 1 ≤ a) (π : D.naut.CG a) : D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π := by
  have hsing : ∀ (π' : D.naut.CG a) w, isoLoc D.nd D.naut [⟨a, π', 1⟩] w = D.naut.locG π' w := by
    intro π' w
    show D.naut.lpSum (spehLoc D.nd D.naut ⟨a, π', 1⟩ w) (D.naut.lpZero w) = _
    rw [D.naut.lpSum_zero]
    unfold spehLoc
    simp [D.naut.lpSum_zero, D.naut.lpTw_zero]
  have h := hAN [⟨a, D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      rw [hsing, hsing, D.naut.locG_tw, D.naut.locG_tw]
      exact (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hT _).2)
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem main : ∀ D : D7, (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → LabDepth D → DepthZ D → ParSurj D := by
  intro D hPar h0 h5 hsplit hLab hDZ i x Sig hX
  obtain ⟨P, -, hB⟩ := hX
  have hT : SumRepresentations.At.TieLP D.nd D.naut := h0.1
  have hAN := h5.1
  set χ := D.naut.etaTinv with hχ
  have htw : twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ =
      twistIso D.nd D.naut Sig χ ++ twistIso D.nd D.naut [muPart D.nd D.naut i] χ := List.map_append

  have hparts : ∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π := by
    intro p hp
    have hm : (⟨p.a, D.naut.tw p.π χ, p.d⟩ : Part D.naut.CG) ∈
        twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ := by
      rw [htw]
      exact List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩)
    obtain ⟨ha, hd, hc⟩ := hB.1 _ hm
    refine ⟨ha, hd, ?_⟩
    have e := tw_back D hT hAN ha p.π
    rw [← e]
    exact D.naut.csd_tw _ _ h0.2.1.1.1 hc

  have hnodup : (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup := by
    have h2 := hB.2.1
    rw [htw, List.map_append] at h2
    have h3 := (List.nodup_append.1 h2).1
    have e : (twistIso D.nd D.naut Sig χ).map (fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)) =
        (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).map
          (fun q => ((⟨q.1.1, D.naut.tw q.1.2 χ⟩ : Σ a, D.naut.CG a), q.2)) := by
      unfold twistIso
      rw [List.map_map, List.map_map]
      rfl
    rw [e] at h3
    exact h3.of_map _

  have hrank : rankIso D.nd D.naut Sig = D.R.r := by
    have hr := hB.2.2.1
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ) =
        rankIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1] at hr
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [muPart, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega

  have hlab : ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).Monic ∧
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r := by
    intro k v
    set w := D.naut.plGw k v with hw
    have hover := D.naut.plGw_over k v
    obtain ⟨hmon, hiff⟩ := hLab k w hover (isoLoc D.nd D.naut Sig w)
    refine ⟨hmon, ?_⟩
    rw [← hrank, ← lpDim_isoLoc]
    apply hiff.2
    intro σ hσ hwild
    have hloc := hB.2.2.2.1 w (hsplit k v)
    have htame := hDZ i P k w hover σ hσ hwild
    rw [← hloc, inePol_twistIso D hT _ w σ hσ, GlobalTheory.RowThetaParam.isoLoc_append, D.naut.inePol_sum] at htame
    have hd1 : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ w
    have hm1 := ((hT w (isoLoc D.nd D.naut Sig w) (isoLoc D.nd D.naut Sig w) _ _ 0 hd1 hd1).2.2.2.2.2 σ hσ).1
    have hm2 := ((hT w (isoLoc D.nd D.naut [muPart D.nd D.naut i] w)
      (isoLoc D.nd D.naut [muPart D.nd D.naut i] w) _ _ 0 hd1 hd1).2.2.2.2.2 σ hσ).1
    have e := eq_pow_of_mul_eq _ _ _ hm1.1 hm2.1 htame
    rw [e, hm1.2]
  exact hPar ⟨Sig, hparts, hnodup, hrank, hlab⟩

end GlobalTheory.ParOfPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulSubMemOfRootsModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem pow_mul_sub_mem_of_roots_mod_pow :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (p : Polynomial R) (x y b lam : R) (n : ℕ),
      p.eval x ∈ I ^ n → p.eval y ∈ I ^ n → x - y ∈ I →
        b * (Polynomial.derivative p).eval x - lam ∈ I → lam ^ n * (x - y) ∈ I ^ n := by
  intro R _ I p x y b lam n hx hy hxy hb
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion p x (y - x)
  have hy' : x + (y - x) = y := by ring
  rw [hy'] at hk
  obtain ⟨d, hdd⟩ : ∃ d, d = y - x := ⟨_, rfl⟩
  rw [← hdd] at hk
  have hd : d ∈ I := by
    have e : d = -(x - y) := by rw [hdd]; ring
    rw [e]; exact I.neg_mem hxy
  obtain ⟨h, hh⟩ : ∃ h, h = (Polynomial.derivative p).eval x + k * d := ⟨_, rfl⟩
  have hdh : d * h ∈ I ^ n := by
    have e : d * h = p.eval y - p.eval x := by rw [hk, hh]; ring
    rw [e]; exact sub_mem hy hx
  obtain ⟨j, hjj⟩ : ∃ j, j = b * h - lam := ⟨_, rfl⟩
  have hj : j ∈ I := by
    have e : j = (b * (Polynomial.derivative p).eval x - lam) + b * k * d := by
      rw [hjj, hh]; ring
    rw [e]; exact add_mem hb (I.mul_mem_left _ hd)
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow lam (-j) n
  have e : lam ^ n * (x - y) = -(b * q * (d * h)) - (-j) ^ n * d := by
    have e1 : lam ^ n = (lam - -j) * q + (-j) ^ n := by rw [← hq]; ring
    have e2 : lam - -j = b * h := by rw [hjj]; ring
    have e3 : x - y = -d := by rw [hdd]; ring
    rw [e1, e2, e3]; ring
  rw [e]
  exact sub_mem (neg_mem (Ideal.mul_mem_left _ _ hdh))
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (neg_mem hj) n))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumAddTwoMulDifferentExponentLeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationJumpSum_add_two_mul_differentExponent_le : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (J : Subgroup (L ≃ₐ[F] L)), jumpSum (wild F L) ⊤ J + 2 * differentExponent ↥(IntermediateField.fixedField J) L ≤ 2 * differentExponent F L := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_add_two_mul_differentExponent_fixedField_le | exact GlobalTheory.PMon.Ram.jumpSum_add_two_mul_differentExponent_fixedField_le | (intros; apply GlobalTheory.PMon.Ram.jumpSum_add_two_mul_differentExponent_fixedField_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationJumpSum_comap_injective : ∀ (G G' : Type) [Group G] [Group G'] (j : G' →* G) (R : ℕ → Subgroup G) (B : Subgroup G), Function.Injective j → jumpSum (fun t => (R t).comap j) ⊤ (B.comap j) = jumpSum R j.range B := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_comap_injective | exact GlobalTheory.PMon.Ram.jumpSum_comap_injective | (intros; apply GlobalTheory.PMon.Ram.jumpSum_comap_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRangeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationJumpSum_eq_sum_range : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) (n : ℕ), Antitone R → (∀ t, t < n ↔ ¬ A ⊓ R t ≤ B) → jumpSum R A B = ∑ t ∈ Finset.range n, Nat.card ↥(A ⊓ R t) := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_eq_sum_range | exact GlobalTheory.PMon.Ram.jumpSum_eq_sum_range | (intros; apply GlobalTheory.PMon.Ram.jumpSum_eq_sum_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumLeAddStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationJumpSum_le_add : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R → (∃ m, R m = ⊥) → B ≤ A → jumpSum R A C ≤ jumpSum R A B + jumpSum R B C := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_le_add | exact GlobalTheory.PMon.Ram.jumpSum_le_add | (intros; apply GlobalTheory.PMon.Ram.jumpSum_le_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumMonoOfLeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationJumpSum_mono_of_le : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R → (∃ m, R m = ⊥) → (∀ t, A ⊓ R t ≤ C → A ⊓ R t ≤ B) → jumpSum R A B ≤ jumpSum R A C := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_mono_of_le | exact GlobalTheory.PMon.Ram.jumpSum_mono_of_le | (intros; apply GlobalTheory.PMon.Ram.jumpSum_mono_of_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionLatticeColumnsConditionLinearIndependStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictionLattice_columns_condition_linearIndependent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → (∀ c, LatC P U x y (colv P ω A₀ c)) ∧ LinearIndependent ℚ_[l] (colv P ω A₀) := by
  first | exact @GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent | exact GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent | (intros; apply GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent <;> assumption)
end

