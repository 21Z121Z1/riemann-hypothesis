import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Columns.Bundle0032
import Formalism.LocalToGlobal.Columns.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90USurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0144
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0436
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0398
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0428
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0429
import Formalism.LocalToGlobal.Columns.RecLevelLocK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0439
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymFrame

variable {D : D7}

def EwAt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ y ∈ X.B.I.Lf, (1 - X.ew) • y ∈ wLf X w

open Classical in

def epsW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.k → VA X.B.I :=
  if EwAt X w then X.bw else fun i => X.bwd (Fin.rev i)

def symVec (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.r → VA X.B.I :=
  GlobalTheory.SeeConjRead.flagV D.R.rS D.R.k D.R.r X.e0 X.f0 (epsW X w) X.z0

def IsMatIn (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} (u : Fin D.R.r → VA X.B.I) (x : X.B.I.Gf)
    (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)) : Prop :=
  ∀ i, X.B.I.fmat x *ᵥ u i - ∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • u j ∈ wLf X w

end GlobalTheory.Mem.SymFrame

end

namespace GlobalTheory.Mem.SymFrame

theorem isMatIn_perm {D : D7} {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)} {g : ℕ}
    (s : Fin D.R.r → VA X.B.I) (x : X.B.I.Gf) (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)) (π : Equiv.Perm (Fin D.R.r))
    (hN : IsMatIn X w (fun j => s (π.symm j)) x N) : IsMatIn X w s x (N.submatrix π π) := by
  intro i
  have h1 := hN (π i)
  rw [← Equiv.sum_comp π] at h1
  simpa [Matrix.submatrix_apply] using h1

theorem mem_unipSym_bc {κ κ' : Type} [CommRing κ] [CommRing κ'] (f : κ ≃+* κ') {r ρ k : ℕ} (u : GL (Fin r) κ) :
    Formalism.UG.bc (f : κ →+* κ') u ∈ unipSym κ' r ρ k ↔ u ∈ unipSym κ r ρ k := by
  have e : ∀ i j, ((Formalism.UG.bc (f : κ →+* κ') u : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j =
      f ((u : Matrix (Fin r) (Fin r) κ) i j) := fun _ _ => rfl
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · have := h1 hij; rw [e] at this; exact f.injective (this.trans (map_zero f).symm)
    · have := h2 i; rw [e] at this; exact f.injective (this.trans (map_one f).symm)
    · have := h3 i j ha hb hc; rw [e] at this; exact f.injective (this.trans (map_zero f).symm)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · show ((Formalism.UG.bc (f : κ →+* κ') u : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j = 0
      rw [e, h1 hij, map_zero]
    · rw [e, h2 i, map_one]
    · rw [e, h3 i j ha hb hc, map_zero]

theorem edgeSum_bc {κ κ' : Type} [CommRing κ] [CommRing κ'] (f : κ ≃+* κ') {r : ℕ} (Ed : Fin r → Fin r → Prop)
    [DecidableRel Ed] (u : GL (Fin r) κ) : edgeSum Ed (Formalism.UG.bc (f : κ →+* κ') u) = f (edgeSum Ed u) := by
  unfold edgeSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · rw [map_zero]

end GlobalTheory.Mem.SymFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownPointPreservesIndexFrames
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2

theorem PtY.mv_dn_facts {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n)
    (p : PtY ST SG Q y) (P : ST) (f' : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal) (v : HeightOneSpectrum (𝓞 X.F))
    (hov : IsOver v P.1) (hne : conjPrime₂ P.1 ≠ P.1) (hconj : IsOver v (conjPrime₂ P.1)) :
    (p.mv (p.1.1.deco.dn P f')).1.2 = p.1.2 ∧ (p.mv (p.1.1.deco.dn P f')).1.1.fr = p.1.1.fr ∧
      Deco.SameOff ST SG v p.1.1.deco.1 (p.mv (p.1.1.deco.dn P f')).1.1.deco.1 := by
  classical

  have key : Deco.SameOff ST SG v p.1.1.deco.1 (p.1.1.deco.dn P f').1 := by
    unfold DecoSet.dn
    split_ifs with hok
    · refine ⟨fun Q hQ => ?_, fun Q hQ => ?_, fun _ _ => rfl⟩
      · have hQP : Q ≠ P.1 := fun h => hQ (by rw [h]; exact hov)
        have hQc : Q ≠ conjPrime₂ P.1 := fun h => hQ (by rw [h]; exact hconj)
        exact ((p.1.1.deco.2.dnN_spec P hne).2.2.1 Q hQP hQc).localization_eq.symm
      · have hQP : Q ≠ P := fun h => hQ (by rw [h]; exact hov)
        show p.1.1.deco.1.f Q = Function.update p.1.1.deco.1.f P f' Q
        rw [Function.update_of_ne hQP]
    · exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

  suffices H : ∀ d : DecoSet X.E n ST SG, Deco.SameOff ST SG v p.1.1.deco.1 d.1 →
      (p.mv d).1.2 = p.1.2 ∧ (p.mv d).1.1.fr = p.1.1.fr ∧
        Deco.SameOff ST SG v p.1.1.deco.1 (p.mv d).1.1.deco.1 from H _ key
  intro d hd
  by_cases h : (∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) ∧ p.1.2 ∈ y.ys d.1.N
  · have e : (p.mv d).1 = ((⟨(d, p.1.1.1.2), h.1⟩ : DecoF X.E n ST SG Q), p.1.2) :=
      congrArg Subtype.val (dif_pos h)
    rw [e]
    exact ⟨rfl, rfl, hd⟩
  · have e : p.mv d = p := dif_neg h
    rw [e]
    exact ⟨rfl, rfl, ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def detU : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) →* U1 (host_cmData R H).sig :=
  (Matrix.GeneralLinearGroup.det.comp (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)).subtype).codRestrict _ fun x =>
    Units.ext (DetLift.det_mul_conj_det _ _ x.2)

def u1Dt (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) →* DtQ H SQ :=
  (normOneIdeleToFinerDeterminantClass H SQ (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
    (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).comp (detU H)

theorem normOneFiniteAdeleDetClass_of_isDetLift (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (a : GlobalTheory.Mem.Chr.Ideles H.E)
    (ha : IsDetLift (host_cmData R H) x.1 a) : u1Dt H SQ x = QuotientGroup.mk a := by
  have e : detU H x = ⟨h90 (host_cmData R H).sig (finAf H.F H.E a), by
      rw [ha]; exact (detU H x).2⟩ := Subtype.ext ha.symm
  show normOneIdeleToFinerDeterminantClass H SQ _ _ _ _ _ (detU H x) = _
  rw [e]
  exact normOneIdeleToFinerDeterminantClass_eq_mk H SQ _ _ _ _ _ _ _ _ (afIso_finAf H.F H.E a).symm

theorem exists_lift (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) : ∃ a : GlobalTheory.Mem.Chr.Ideles H.E, IsDetLift (host_cmData R H) x.1 a :=
  DetLift.exists_isDetLift R H 1 x.1 x.2

theorem exists_of_idele (a : GlobalTheory.Mem.Chr.Ideles H.E) : ∃ x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H), IsDetLift (host_cmData R H) x.1 a := by
  have hu : h90 (host_cmData R H).sig (finAf H.F H.E a) ∈ U1 (host_cmData R H).sig :=
    (DetClass.exists_detClass R H (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
      (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).1.le ⟨_, rfl⟩
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 1) (h90 (host_cmData R H).sig (finAf H.F H.E a)), ?_⟩, ?_⟩
  · show Formalism.UG.cT _ _ * _ * _ = _
    have hz := congrArg Units.val (show (h90 (host_cmData R H).sig (finAf H.F H.E a)) * conjId (host_cmData R H).sig (h90 (host_cmData R H).sig (finAf H.F H.E a)) = 1 from hu)
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Formalism.UG.cT, Matrix.mul_apply]
    exact (mul_comm _ _).trans hz
  · exact Units.ext (by simp)

theorem normOneFiniteAdeleDetClass_surjective (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) : Function.Surjective (u1Dt H SQ) := fun t => by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨x, hx⟩ := exists_of_idele H a
  exact ⟨x, normOneFiniteAdeleDetClass_of_isDetLift H SQ x a hx⟩

end GlobalTheory.Mem.Col2.FullDt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormRationality
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

noncomputable section

namespace GlobalTheory.OneMapRef.IoCmp

theorem pure_rename {ι ι' κ X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {A' : ι' → (X → ℂ) → (X → ℂ)} {g : X → ℂ}
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (e : κ → ι) (e' : κ → ι') (h : ∀ k, A (e k) = A' (e' k)) (Q : MvPolynomial κ ℂ) :
    pureTensorL A g (MvPolynomial.rename e Q) = pureTensorL A' g (MvPolynomial.rename e' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, MvPolynomial.rename_C, ← mul_one (MvPolynomial.C a : MvPolynomial ι ℂ),
      ← mul_one (MvPolynomial.C a : MvPolynomial ι' ℂ), MvPolynomial.C_mul', MvPolynomial.C_mul', map_smul, map_smul,
      GlobalTheory.FockIndep.pure_one, GlobalTheory.FockIndep.pure_one]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, map_mul (MvPolynomial.rename e), map_mul (MvPolynomial.rename e'), MvPolynomial.rename_X, MvPolynomial.rename_X, hX, hX', hp, h]

theorem aeval_scale {L Y : Type} (f : L → Y) (s : ℂ) {N : ℕ} {Q : MvPolynomial L ℂ} (hQ : Q.IsHomogeneous N) :
    MvPolynomial.aeval (fun ℓ => MvPolynomial.C s * MvPolynomial.X (f ℓ)) Q =
      MvPolynomial.C (s ^ N) * MvPolynomial.rename f Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : m.degree = N := by
    have := hQ (MvPolynomial.mem_support_iff.1 hm)
    rwa [Finsupp.degree_eq_weight_one]
  rw [MvPolynomial.rename_eq_aeval, MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← hd]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Function.comp_apply, map_pow,
    Finsupp.degree_apply]
  ring

theorem isHomogeneous_of_span {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop)
    (a : T → ℕ → ℕ) {P : MvPolynomial (Letter T r n) k} (hP : P ∈ Submodule.span k (HHa r n k cc isX a)) :
    P.IsHomogeneous (∑ σ, ∑ i : Fin (r σ), a σ i) := by
  refine (Submodule.span_le (p := MvPolynomial.homogeneousSubmodule _ k _)).2 (fun Q hQ m hm => ?_) hP
  have h := hQ.2.2 m (MvPolynomial.mem_support_iff.2 hm)
  refine Eq.trans (b := m.degree) (by rw [Finsupp.degree_eq_weight_one]; rfl) ?_
  rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => h σ i

theorem lieFac_eq_pow {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (hx : 0 < xiR D)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    lieFac Dw (xiR D) a = (Real.sqrt (2 * Real.pi * xiR D))⁻¹ ^ (∑ σ, ∑ i : Fin (Dw.mult σ), a (σ, i)) := by
  have h : 0 < 2 * Real.pi * xiR D := by positivity
  have h2 : (Real.sqrt (2 * Real.pi * xiR D))⁻¹ = Real.exp (-(Real.log (2 * Real.pi * xiR D) / 2)) := by
    rw [Real.exp_neg, ← Real.log_sqrt h.le, Real.exp_log (Real.sqrt_pos.2 h)]
  rw [h2, ← Real.exp_nat_mul, lieFac]
  congr 1
  push_cast
  ring

theorem two_div_fockScale (D : D7) (τ : D.what₂.Tau) : 2 / fockScale D τ = (Real.sqrt (2 * Real.pi * xiR D))⁻¹ := by
  rw [fockScale, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq, div_mul_cancel_left₀ two_ne_zero]

theorem unitMap_submatrix {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) (π : Fin m → Fin m)
    (c : Fin m) (j : Fin n) :
    Formalism.IndefR.Datum.unitMap B (B'.submatrix id π) c j = Formalism.IndefR.Datum.unitMap B B' (π c) j := by
  unfold Formalism.IndefR.Datum.unitMap
  congr 1
  ext a b
  by_cases h : b = j
  · subst h
    simp
  · simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ h]

theorem pureTensorO_rename {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hS : ∀ τ, IsCartanInv (gramAt D S τ) 1)
    (hT : ∀ τ, IsCartanInv (gramAt D T τ) (s τ)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (Z Z' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (π : D.what₂.Tau → Fin T.rank → Fin T.rank) (hZ : ∀ τ, Z' τ = (Z τ).submatrix id (π τ)) {κ : Type} (ρ : κ → D.what₂.Tau)
    (c : κ → Fin T.rank) (b : κ → Fin S.rank) (Q : MvPolynomial κ ℂ) :
    pureTensorO ψ θ S T (fun _ => 1) s B Z f (MvPolynomial.rename (fun k => (ρ k, π (ρ k) (c k), b k)) Q) =
      pureTensorO ψ θ S T (fun _ => 1) s B Z' f (MvPolynomial.rename (fun k => (ρ k, c k, b k)) Q) := by
  have hX : ∀ B' v Q, pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B') f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B' v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B') f Q) := fun B' v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  refine pure_rename (hX Z) (hX Z') _ _ (fun k => ?_) Q
  simp only [aPlusAll, hZ, unitMap_submatrix]

end GlobalTheory.OneMapRef.IoCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsRowOfEigensystemIndexGoodCharacters
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3

theorem partsRec_of_eig : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → (∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix) (e : D.what₂.LL →+* ℂ), D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) → Xd.logLam ((i : ℕ) + 1) π e = Real.log (R.lam3 i A3.A.μ0 c (InfinitePlace.mk e))) → ∃ (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PartsRec R.toRealDat F.lv2 Y.tupT Y.hm Y.PY Y.PW Y.eFT E labPi piOf Y.Ish.prt Y.IL.prtW := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Xd hP hH hHost hgen hLam
  have e1 := GlobalTheory.T.exists_sphericalEigensystem_firstLift_baseLevel hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost hgen
  have e2 := GlobalTheory.Mem.EigCarry.carries_of_hasEig hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e3 := GlobalTheory.Mem.R3.IsotPart.isot_le_part hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e4 := GlobalTheory.Mem.R3.prt_le_hPart_of_carries hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e5 := GlobalTheory.Mem.R3.prtW_le_hPart hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have hc : Formalism.L2.Col.PairComm (A3.fam3.F.R A3.fam3.F.μ0).op := (hH.ok.ok2.what₂ A3.fam3.F.μ0).comm
  classical

  have hE : ∀ π, HasEig R F Y π (eigOfType R F Y π) := fun π => hasEig_eigOfType (e1 π)
  have hK : ∀ π, ∃ p, R.Carries p (eigOfType R F Y π) := fun π => e2 π _ (hE π)
  let Pi : Type := Set.range (eigOfType R F Y)
  have hPi : ∀ c : Pi, ∃ p, R.Carries p c.1 := by
    rintro ⟨c, π, rfl⟩
    exact hK π
  let labP : Pi → A3.fam3.base3.Ix := fun c => (hPi c).choose
  let E : EigIdx D Xd :=
    { Pi := Pi
      fin := Set.fintypeRange _
      dec := Classical.decEq _
      cOf := fun π => ⟨eigOfType R F Y π, π, rfl⟩
      lam_const := by
        intro j hj π π' e h1 h2 hcc
        have hc' : eigOfType R F Y π = eigOfType R F Y π' := congrArg Subtype.val hcc
        obtain ⟨p, hp⟩ := hK π
        have hp' : R.Carries p (eigOfType R F Y π') := hc' ▸ hp
        have hj' : 1 ≤ j ∧ j ≤ D.R.m := Finset.mem_Icc.1 hj
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        have hk : k < D.R.m := by omega
        have a1 := hLam ⟨k, hk⟩ π p e h1 (e3 π _ p (hE π) hp ⟨k, hk⟩)
        have a2 := hLam ⟨k, hk⟩ π' p e h2 (e3 π' _ p (hE π') hp' ⟨k, hk⟩)
        exact a1.trans a2.symm }
  refine ⟨E, fun c => A3.fam3.toIx2 hc (labP c), Subtype.val, ?_⟩
  refine ⟨fun π => rfl, Subtype.val_injective, ?_, ?_⟩
  · intro π
    exact e4 π _ _ (hE π) (hPi _).choose_spec
  · intro i π
    have h5 := e5 π _ _ (hE π) (hPi (E.cOf π)).choose_spec i
    exact h5

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionEqBasePiMulIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.PiDiv

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ST : Finset (Pl E)} {π : 𝓞 E}

theorem notMem_of_notMem (h : BasePi ST π) {w : Pl E} (hw : w ∉ ST) : π ∉ w.asIdeal := by
  intro hπ
  have hle : ST.inf (fun P : Pl E => P.asIdeal) ≤ w.asIdeal := by
    intro x hx
    have hx' : ∀ P ∈ ST, x ∈ P.asIdeal := fun P hP => (Finset.inf_le hP : ST.inf (fun P : Pl E => P.asIdeal) ≤ P.asIdeal) hx
    obtain ⟨c, rfl⟩ := (h.dvd x).1 hx'
    exact Ideal.mul_mem_right _ _ hπ
  obtain ⟨P, hP, hPw⟩ := (Ideal.IsPrime.inf_le' w.isPrime).1 hle
  have e : P.asIdeal = w.asIdeal := P.isMaximal.eq_of_le w.isPrime.ne_top hPw
  exact hw (HeightOneSpectrum.ext e ▸ hP)

theorem exp_neg_one_le (h : BasePi ST π) {w : Pl E} (hw : w ∈ ST) : WithZero.exp (-1) ≤ w.intValuation π := by
  classical
  obtain ⟨b, hb⟩ := w.intValuation_exists_uniformizer
  obtain ⟨a, ha⟩ := crtPl ST (fun P => if P = w then 1 else 0)
  have haw : a ∉ w.asIdeal := by
    intro haw
    have h1 := ha w hw
    rw [if_pos rfl] at h1
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.sub_mem _ haw h1))
  have hbw : b ∈ w.asIdeal := (w.intValuation_lt_one_iff_mem b).1 (by rw [hb, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
  have hab : ∀ P ∈ ST, a * b ∈ P.asIdeal := by
    intro P hP
    by_cases hPw : P = w
    · subst hPw; exact Ideal.mul_mem_left _ _ hbw
    · have h1 := ha P hP
      rw [if_neg hPw, sub_zero] at h1
      exact Ideal.mul_mem_right _ _ h1
  obtain ⟨c, hc⟩ := (h.dvd _).1 hab
  have hv : w.intValuation (a * b) = WithZero.exp (-1) := by
    rw [map_mul, hb, HeightOneSpectrum.intValuation_eq_one_iff.2 haw, one_mul]
  rw [← hv, hc, map_mul]
  exact mul_le_of_le_one_right' (w.intValuation_le_one c)

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem prV_inclE (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) x) = inclE (F := F) (v.adicCompletion F) x := by
  simp [prV, inclE, Algebra.TensorProduct.map_tmul]

end GlobalTheory.Mem.Col2.PiDiv

open GlobalTheory.Mem.Col2.PiDiv in

theorem GlobalTheory.Mem.Col2.prV_eq_pi_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), z ∈ Formalism.L2.Herm.intAf F E → (∀ P ∈ ST, Valued.v (adAt F P z) < 1) → ∃ s ∈ intV E v, prV (E := E) v z = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s := by
  intro F E _ _ _ _ _ _ ST π hπ v z hz hP
  set e : E := algebraMap (𝓞 E) E π with he_def
  have he : e ≠ 0 := hπ.coe_ne_zero
  have hzR : z ∈ RInt F E := hz
  refine ⟨prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e⁻¹ * z), ?_, ?_⟩
  · refine (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v _).2.2 fun w _ => ?_
    rw [map_mul, adAt_inclE, map_mul, valued_algebraMap, map_inv₀]
    have hz1 : Valued.v (adAt F w z) ≤ 1 := by rw [adAt_apply]; exact (mem_rInt_iff F E z).1 hzR w
    have hv0 : 0 < w.valuation E e := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 he
    rw [inv_mul_le_one₀ hv0]
    have hve : w.valuation E e = w.intValuation π := HeightOneSpectrum.valuation_of_algebraMap w π
    by_cases hw : w ∈ ST
    · exact (le_exp_neg_one_of_lt_one (hP w hw)).trans (hve ▸ exp_neg_one_le hπ hw)
    · rw [hve, HeightOneSpectrum.intValuation_eq_one_iff.2 (notMem_of_notMem hπ hw)]
      exact hz1
  · rw [map_mul, prV_inclE, ← mul_assoc, ← map_mul, mul_inv_cancel₀ he, map_one, one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SphericalVectorFixedLocalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_vector_fixed_local : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E)
    (w : PlE D.host) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → ∀ J : Subgroup (GAf D.host.E D.R.nV),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)) → ∀ f ∈ π.S, f ≠ 0 →
    (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) → ∀ c : ℕ → ℂ,
    (∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) → ∀ x, GlobalTheory.AutQuot.LocAt π w x →
    ((GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).unr ∧
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      (Multiset.map (fun α => X - Polynomial.C α)
        ((GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).frobEig).prod := by
  first | exact @GlobalTheory.HeckeFrob.locPol_eq | exact GlobalTheory.HeckeFrob.locPol_eq | (intros; apply GlobalTheory.HeckeFrob.locPol_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardFrameConjugateCloseStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_frame_conjugate_close : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1 := by
  first | exact @GlobalTheory.ConjLt.frame_mat_sub_one_lt | exact GlobalTheory.ConjLt.frame_mat_sub_one_lt | (intros; apply GlobalTheory.ConjLt.frame_mat_sub_one_lt <;> assumption)
end

