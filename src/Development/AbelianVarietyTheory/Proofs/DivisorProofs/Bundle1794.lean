import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0035
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealMulConjEqGramDetSelfDual
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMapApply
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open MeasureTheory
open GlobalTheory.Mem.Isom
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri Rig)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriMove

variable {D : D7}

def rdx {K : Type} [Zero K] [One K] {m n : ℕ} (h : m = n) : Matrix (Fin m) (Fin n) K :=
  (1 : Matrix (Fin m) (Fin m) K).submatrix id (finCongr h).symm

def rdi {K : Type} [Zero K] [One K] {m n : ℕ} (h : m = n) : Matrix (Fin n) (Fin m) K :=
  (1 : Matrix (Fin m) (Fin m) K).submatrix (finCongr h).symm id

theorem rdx_rdi {K : Type} [CommRing K] {m n : ℕ} (h : m = n) : rdx (K := K) h * rdi (K := K) h = 1 := by
  subst h
  ext i j
  simp [rdx, rdi, Matrix.one_apply]

theorem rdi_rdx {K : Type} [CommRing K] {m n : ℕ} (h : m = n) : rdi (K := K) h * rdx (K := K) h = 1 := by
  subst h
  ext i j
  simp [rdx, rdi, Matrix.one_apply]

def glMove {K : Type} [CommRing K] {m n : ℕ} (h : m = n) (P : Matrix (Fin n) (Fin m) K) (Q : Matrix (Fin m) (Fin n) K)
    (PQ : P * Q = 1) (QP : Q * P = 1) (x : GL (Fin m) K) : GL (Fin n) K where
  val := HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h)
  inv := HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q
  val_inv := by
    have e1 := rdx_rdi (K := K) h
    have e2 : (x.1 : Matrix (Fin m) (Fin m) K) * x.2 = 1 := x.val_inv
    calc HMul.hMul (HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h))
          (HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q)
        = HMul.hMul (HMul.hMul P (HMul.hMul (HMul.hMul (x.1 : Matrix (Fin m) (Fin m) K) (HMul.hMul (rdx (K := K) h) (rdi (K := K) h))) (x.2 : Matrix (Fin m) (Fin m) K))) Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.mul_one, e2, Matrix.mul_one, PQ]
  inv_val := by
    have e1 := rdi_rdx (K := K) h
    have e2 : (x.2 : Matrix (Fin m) (Fin m) K) * x.1 = 1 := x.inv_val
    calc HMul.hMul (HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q)
          (HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h))
        = HMul.hMul (HMul.hMul (rdi (K := K) h) (HMul.hMul (HMul.hMul (x.2 : Matrix (Fin m) (Fin m) K) (HMul.hMul Q P)) (x.1 : Matrix (Fin m) (Fin m) K))) (rdx (K := K) h) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [QP, Matrix.mul_one, e2, Matrix.mul_one, e1]

variable {S S' T T' : HSp D}

def fP (I : IsoMat S S') : Matrix (Fin S'.rank) (Fin S.rank) (Lev.EAf D) := I.P.map (eToEAf D)

def fQ (I : IsoMat S S') : Matrix (Fin S.rank) (Fin S'.rank) (Lev.EAf D) := I.Q.map (eToEAf D)

theorem fP_fQ (I : IsoMat S S') : fP I * fQ I = 1 := by
  rw [fP, fQ, ← Matrix.map_mul, I.PQ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem fQ_fP (I : IsoMat S S') : fQ I * fP I = 1 := by
  rw [fP, fQ, ← Matrix.map_mul, I.QP, Matrix.map_one _ (map_zero _) (map_one _)]

def betaMove (I : IsoMat S S') (β : GL (Fin S.rank) (Lev.EAf D)) : GL (Fin S'.rank) (Lev.EAf D) :=
  glMove I.rank_eq (fP I) (fQ I) (fP_fQ I) (fQ_fP I) β

def latMove (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E) :=
  Λ.map ((Matrix.mulVecLin I.P).restrictScalars (𝓞 D.host.E))

def cartMove (I : IsoMat S S') (τ : D.what₂.Tau) (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    Matrix (Fin S'.rank) (Fin S'.rank) ℂ := I.pT τ * s * I.qT τ

def basMove (I : IsoMat S S') (τ : D.what₂.Tau) (B : Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    Matrix (Fin S'.rank) (Fin S'.rank) ℂ := I.pT τ * B * rdx I.rank_eq

def rigMove (I : IsoMat S S') (r : Rig S) : Rig S' where
  Λ := latMove I r.Λ
  β := betaMove I r.β
  s τ := cartMove I τ (r.s τ)
  B τ := basMove I τ (r.B τ)

def homMap (IS : IsoMat S S') (IT : IsoMat T T') : WO S T ≃+ WO S' T' where
  toFun x := HMul.hMul (HMul.hMul IT.aP x) IS.aQ
  invFun y := HMul.hMul (HMul.hMul IT.aQ y) IS.aP
  left_inv x := by
    show HMul.hMul (HMul.hMul IT.aQ (HMul.hMul (HMul.hMul IT.aP x) IS.aQ)) IS.aP = x
    calc _ = HMul.hMul (HMul.hMul (HMul.hMul IT.aQ IT.aP) x) (HMul.hMul IS.aQ IS.aP) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [IT.aQ_aP, IS.aQ_aP, Matrix.one_mul, Matrix.mul_one]
  right_inv y := by
    show HMul.hMul (HMul.hMul IT.aP (HMul.hMul (HMul.hMul IT.aQ y) IS.aP)) IS.aQ = y
    calc _ = HMul.hMul (HMul.hMul (HMul.hMul IT.aP IT.aQ) y) (HMul.hMul IS.aP IS.aQ) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [IT.aP_aQ, IS.aP_aQ, Matrix.one_mul, Matrix.mul_one]
  map_add' x y := by
    show HMul.hMul (HMul.hMul IT.aP (x + y)) IS.aQ = HMul.hMul (HMul.hMul IT.aP x) IS.aQ + HMul.hMul (HMul.hMul IT.aP y) IS.aQ
    rw [Matrix.mul_add, Matrix.add_mul]

theorem homMap_apply (IS : IsoMat S S') (IT : IsoMat T T') (x : WO S T) :
    homMap IS IT x = HMul.hMul (HMul.hMul IT.aP x) IS.aQ := rfl

def trH (IS : IsoMat S S') (IT : IsoMat T T') (f : WO S T → ℂ) : WO S' T' → ℂ := fun w => f ((homMap IS IT).symm w)

def trLE (IS : IsoMat S S') (IT : IsoMat T T') : (WO S T → ℂ) ≃ₗ[ℂ] (WO S' T' → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (homMap IS IT).symm.toEquiv

def omH (IS : IsoMat S S') (IT : IsoMat T T') (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ) :=
  (trLE IS IT).conjRingEquiv.toMulEquiv.toMonoidHom.comp (om.comp (IS.kap.symm.toMonoidHom.prodMap IT.kap.symm.toMonoidHom))

theorem omH_apply (IS : IsoMat S S') (IT : IsoMat T T') (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S') (h : GA D T') (f : WO S' T' → ℂ) :
    omH IS IT om (g, h) f = trH IS IT (om (IS.kap.symm g, IT.kap.symm h) (trH IS.symm IT.symm f)) := rfl

def polMove {m n m' n' : ℕ} (hm : m = m') (hn : n = n') :
    MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m' n') ℂ :=
  MvPolynomial.rename fun k => (k.1, finCongr hm k.2.1, finCongr hn k.2.2)

variable {T₀ : Type} {A A' WW B B' WW₁ : HSp D}

def triMove (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) : Tri T₀ A A' WW where
  rA := rigMove IA Y.rA
  rA' := rigMove IA' Y.rA'
  rW := rigMove IW Y.rW
  ω t := omH IA IW (Y.ω t)
  ω' t := omH IA' IW (Y.ω' t)
  vac := trH IA IW Y.vac
  vac' := trH IA' IW Y.vac'
  e := Y.e
  c := Y.c
  f t := trH IA IW (Y.f t)
  f' t := trH IA' IW (Y.f' t)
  m := Y.m.map IA.kap
  fd := IA.kap.symm ⁻¹' Y.fd
  m' := Y.m'.map IA'.kap
  fd' := IA'.kap.symm ⁻¹' Y.fd'

end GlobalTheory.TriMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityForTransport
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.HoweTransport

open GlobalTheory.Published GlobalTheory.PRep

section Sub

variable {H H' T : Type} [Group H] [Group H'] [AddCommGroup T] [Module ℂ T]

def subIso (e : H ≃* H') (ρ : Representation ℂ H' T) :
    Subrepresentation (ρ.comp e.toMonoidHom : Representation ℂ H T) ≃o Subrepresentation ρ where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (e.symm g) hv
    simpa using h⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (e g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem irr_comp (e : H ≃* H') {ρ : Representation ℂ H' T} (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom : Representation ℂ H T) := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact (subIso e ρ).isSimpleOrder

theorem coatom_comp (e : H ≃* H') {ρ : Representation ℂ H' T}
    (h : ∀ N N' : Subrepresentation ρ, IsCoatom N → IsCoatom N' → N = N') :
    ∀ N N' : Subrepresentation (ρ.comp e.toMonoidHom : Representation ℂ H T), IsCoatom N → IsCoatom N' → N = N' := by
  intro N N' hN hN'
  apply (subIso e ρ).injective
  exact h _ _ (((subIso e ρ).isCoatom_iff N).2 hN) (((subIso e ρ).isCoatom_iff N').2 hN')

def modIso (e : H ≃* H') (ρ : Representation ℂ H' T) :
    Submodule (MonoidAlgebra ℂ H) (Representation.asModule (ρ.comp e.toMonoidHom : Representation ℂ H T)) ≃o
      Submodule (MonoidAlgebra ℂ H') ρ.asModule :=
  (Subrepresentation.subrepresentationSubmoduleOrderIso.symm.trans (subIso e ρ)).trans
    Subrepresentation.subrepresentationSubmoduleOrderIso

theorem finLen_comp (e : H ≃* H') {ρ : Representation ℂ H' T}
    (h : IsFiniteLength (MonoidAlgebra ℂ H') ρ.asModule) :
    IsFiniteLength (MonoidAlgebra ℂ H) (Representation.asModule (ρ.comp e.toMonoidHom : Representation ℂ H T)) := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
  obtain ⟨h1, h2⟩ := h
  rw [isNoetherian_iff'] at h1 ⊢
  refine ⟨(modIso e ρ).strictMono.wellFoundedGT, ?_⟩
  haveI := h2
  exact (modIso e ρ).strictMono.wellFoundedLT

end Sub

section Top

variable {G G' V : Type} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G'] [AddCommGroup V] [Module ℂ V]

theorem smooth_comp (e : G' →* G) (he : Continuous e) {π : Representation ℂ G V} (h : IsSmooth π) :
    IsSmooth (π.comp e : Representation ℂ G' V) := fun v => (h v).preimage he

theorem fixed_comp (e : G' ≃* G) (π : Representation ℂ G V) (K : Subgroup G') :
    fixed (π.comp e.toMonoidHom : Representation ℂ G' V) K = fixed π (K.comap e.symm.toMonoidHom) := by
  ext v
  simp only [fixed, eig, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro hv k
    have := hv ⟨e.symm k, k.2⟩
    simpa using this
  · intro hv k
    have := hv ⟨e k, by simp [Subgroup.mem_comap]⟩
    simpa using this

theorem admissible_comp_eval (e : G' ≃* G) (he : Continuous e) (he' : Continuous e.symm) {π : Representation ℂ G V}
    (h : IsAdmissible π) : IsAdmissible (π.comp e.toMonoidHom : Representation ℂ G' V) := by
  refine ⟨smooth_comp e.toMonoidHom he h.1, fun K hKo hKc => ?_⟩
  rw [fixed_comp]
  refine h.2 _ ?_ ?_
  · have : ((K.comap e.symm.toMonoidHom : Subgroup G) : Set G) = e.symm ⁻¹' (K : Set G') := rfl
    rw [this]
    exact hKo.preimage he'
  · have : ((K.comap e.symm.toMonoidHom : Subgroup G) : Set G) = e '' (K : Set G') := by
      ext x
      simp only [Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe, Set.mem_image, MulEquiv.coe_toMonoidHom]
      exact ⟨fun hx => ⟨e.symm x, hx, by simp⟩, fun ⟨y, hy, hyx⟩ => by rw [← hyx]; simpa using hy⟩
    rw [this]
    exact hKc.image he

end Top

end GlobalTheory.HoweLocal.HoweTransport

namespace GlobalTheory.HoweLocal.HoweTransport

open GlobalTheory.Published GlobalTheory.PRep

section HoweDuality

variable {G G' H H' Y V T : Type} [Group G] [Group G'] [Group H] [Group H'] [TopologicalSpace Y]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℂ T]

theorem left_iff (eG : G ≃* G') (eH : H ≃* H') (om : G' × H' →* Module.End ℂ (Y → ℂ))
    (π : Representation ℂ G V) (f : SB Y →ₗ[ℂ] V) :
    IsLeftHom (om.comp (eG.toMonoidHom.prodMap eH.toMonoidHom)) π f ↔
      IsLeftHom om (π.comp eG.symm.toMonoidHom) f := by
  constructor
  · intro h g φ φ₁ hφ
    have := h (eG.symm g) φ φ₁ (by simpa using hφ)
    simpa using this
  · intro h g φ φ₁ hφ
    have := h (eG g) φ φ₁ (by simpa using hφ)
    simpa using this

theorem pair_to (eG : G ≃* G') (eH : H ≃* H') (om : G' × H' →* Module.End ℂ (Y → ℂ))
    (π : Representation ℂ G V) (τ : Representation ℂ H T) (f : SB Y →ₗ[ℂ] V ⊗[ℂ] T)
    (h : IsPairHom (om.comp (eG.toMonoidHom.prodMap eH.toMonoidHom)) π τ f) :
    IsPairHom om (π.comp eG.symm.toMonoidHom) (τ.comp eH.symm.toMonoidHom) f := by
  intro g k φ φ₁ hφ
  have := h (eG.symm g) (eH.symm k) φ φ₁ (by simpa using hφ)
  simpa using this

theorem pair_from (eG : G ≃* G') (eH : H ≃* H') (om : G' × H' →* Module.End ℂ (Y → ℂ))
    (π : Representation ℂ G V) (τ : Representation ℂ H' T) (f : SB Y →ₗ[ℂ] V ⊗[ℂ] T)
    (h : IsPairHom om (π.comp eG.symm.toMonoidHom) τ f) :
    IsPairHom (om.comp (eG.toMonoidHom.prodMap eH.toMonoidHom)) π (τ.comp eH.toMonoidHom) f := by
  intro g k φ φ₁ hφ
  have := h (eG g) (eH k) φ φ₁ (by simpa using hφ)
  simpa using this

theorem equiv_back {V' : Type} [AddCommGroup V'] [Module ℂ V'] (eG : G ≃* G') {π : Representation ℂ G V}
    {π' : Representation ℂ G V'}
    (e : Representation.Equiv (π.comp eG.symm.toMonoidHom : Representation ℂ G' V)
      (π'.comp eG.symm.toMonoidHom : Representation ℂ G' V')) :
    Nonempty (π.Equiv π') := by
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (eG g) v
  simp only [LinearMap.comp_apply]
  change e.toIntertwiningMap (π g v) = π' g (e.toIntertwiningMap v)
  simpa using h1

end HoweDuality

end GlobalTheory.HoweLocal.HoweTransport

namespace GlobalTheory.HoweLocal.HoweTransport

open GlobalTheory.Published GlobalTheory.PRep

theorem howeDualityFor_transport : ∀ {G G' H H' Y : Type} [Group G] [Group G'] [Group H] [Group H'] [TopologicalSpace G] [TopologicalSpace G']
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace Y] (eG : G ≃* G') (eH : H ≃* H'),
    Continuous eG → Continuous eG.symm → Continuous eH → Continuous eH.symm →
    ∀ om : G' × H' →* Module.End ℂ (Y → ℂ), GlobalTheory.Published.HoweDualityFor om →
      GlobalTheory.Published.HoweDualityFor (om.comp (eG.toMonoidHom.prodMap eH.toMonoidHom)) := by
  intro G G' H H' Y _ _ _ _ _ _ _ _ _ eG eH hG hG' hH hH' om hom
  have hGs : Continuous eG.symm.symm := by simpa using hG
  intro V _ _ π hπ hA
  obtain ⟨⟨T, iT1, iT2, Θ, p, ⟨hP, hSur, hK⟩, hS, hF, hC⟩, h2⟩ :=
    hom V (π.comp eG.symm.toMonoidHom) (irr_comp eG.symm hπ) (admissible_comp_eval eG.symm hG' hGs hA)
  refine ⟨⟨T, iT1, iT2, Θ.comp eH.toMonoidHom, p, ⟨pair_from eG eH om π Θ p hP, hSur, fun φ => ?_⟩,
    smooth_comp eH.toMonoidHom hH hS, finLen_comp eH hF, coatom_comp eH hC⟩, ?_⟩
  · rw [hK φ]
    simp only [left_iff]
  · intro T _ _ τ hτ hτs f hf hf0
    obtain ⟨h2a, h2b⟩ := h2 T (τ.comp eH.symm.toMonoidHom) (irr_comp eH.symm hτ)
      (smooth_comp eH.symm.toMonoidHom hH' hτs) f (pair_to eG eH om π τ f hf) hf0
    refine ⟨fun f' hf' => h2a f' (pair_to eG eH om π τ f' hf'), fun V' _ _ π₂ hπ₂ hA₂ f' hf' hf'0 => ?_⟩
    obtain ⟨e⟩ := h2b V' (π₂.comp eG.symm.toMonoidHom) (irr_comp eG.symm hπ₂) (admissible_comp_eval eG.symm hG' hGs hA₂) f'
      (pair_to eG eH om π₂ τ f' hf') hf'0
    exact equiv_back eG e

end GlobalTheory.HoweLocal.HoweTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaSum
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FramesAtReal

theorem framesEx_of_realisation : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : RealT Rc P Dcf Spf Zscf S Ks), RealPins Q → Q.FramesEx := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S Ks _ _ _ Q _
  exact GlobalTheory.FramesExistLev.selfDual_frames_normal_at_level_places_of_charFrame D Q.Rl.C Q.Rl.Pg Q.charW.base.lev.Pg

end GlobalTheory.FramesAtReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealMulConjEqGramDetSelfDualStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_ideal_mul_conj_eq_gram_det_selfDual : ∀ (E : Type) [Field E] [NumberField E] (bar : 𝓞 E →+* 𝓞 E) (barE : E →+* E),
    (∀ x : 𝓞 E, barE x = ((bar x : 𝓞 E) : E)) → ∀ (p : ℕ) (G : Matrix (Fin p) (Fin p) (𝓞 E))
    (Λ : Submodule (𝓞 E) (Fin p → E)), Λ.FG → (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) →
    (∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (G a b : E) * barE (d b)) →
    GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E))) *
      (GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))).map bar =
      Ideal.span {G.det} := by
  first | exact @GlobalTheory.SelfDualIndex.idx_mul_map_bar_eq | exact GlobalTheory.SelfDualIndex.idx_mul_map_bar_eq | (intros; apply GlobalTheory.SelfDualIndex.idx_mul_map_bar_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorSmallCosetHalfIsSchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_smallCoset_half_isSchwartzBruhat : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ) (r : WO S T), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e P → IsHalf e r → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (cosLoc P e βT βS n r) := by
  first | exact @GlobalTheory.FunObj.CosSB.isSBHalf_cosLoc | exact GlobalTheory.FunObj.CosSB.isSBHalf_cosLoc | (intros; apply GlobalTheory.FunObj.CosSB.isSBHalf_cosLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExistsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_local_field_data_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : Valued L (WithZero (Multiplicative ℤ))) (_ : CompleteSpace L)
      (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ AE F E),
      Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧ (Valued.v δ = 1 ∧ σL δ = -δ) ∧
      (∀ x ∈ Formalism.UG.intL L, σL x = x → ψL x = 1) ∧ (∃ x ∈ Formalism.UG.intL L, σL x = x ∧ ψL (ϖ⁻¹ * x) ≠ 1) ∧
      Function.Injective ι ∧ (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) ∧
      (∀ x y, ι (x * y) = ι x * ι y) ∧ (∀ x, ι (σL x) = cA σ (ι x)) ∧
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) ∧
      (∀ x, B.ψ (Algebra.trace (AF F) (AE F E) (ι x)) = ψL (x + σL x)) := by
  first | exact @GlobalTheory.InertLocField.field_data | exact GlobalTheory.InertLocField.field_data | (intros; apply GlobalTheory.InertLocField.field_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldValuationRingStrictlyHenselianStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaFixedField_valuationRing_strictlyHenselian : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → GlobalTheory.SS.SH (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) (IntermediateField.fixedField (inertia K V)) ∧ ∃ f : R →+* V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω), (∀ r : R, ((f r : IntermediateField.fixedField (inertia K V)) : Ω) = algebraMap K Ω (algebraMap R K r)) ∧ ∀ π : R, Irreducible π → Irreducible (f π) := by
  first | exact @GlobalTheory.InertiaFixedSH.inertiaFixed_strictlyHenselian | exact GlobalTheory.InertiaFixedSH.inertiaFixed_strictlyHenselian | (intros; apply GlobalTheory.InertiaFixedSH.inertiaFixed_strictlyHenselian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaKernelDefiniteSeesawStage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.SqTower

theorem integrableOn_ker'_of_stage_zero : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (p : ℕ)
    (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
    ∀ (t : T) (P' : PolF D WW.rank A'.rank) (h : GA D WW), MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m' := by
  intro D T Lc sc G W i j p A A' WW X hX t P' h
  obtain ⟨-, -, -, -, -, hA', -, hIs⟩ := hX
  have hom : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hIs.weil' t
  have hpos : ∀ τ, (gramAt D A' τ).PosDef := fun τ =>
    GlobalTheory.DefiniteQuotient.posDef_of_signature (hA' τ)
  have hf : IsThetaFunO W.ψ A' WW (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P') :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hIs.isVac'.1 hIs.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
      (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hIs.isVac'.1 hIs.isVac'.2.inf (hIs.snd t) hIs.isVac'.2.theta) P'
  have key := GlobalTheory.DefiniteQuotient.integrableOn_theta D W.ψ hom.std A' WW _ _ (X.ω' t) hom hpos ℂ
    (LinearMap.toSpanSingleton ℂ _ (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P'))
    (fun x => GlobalTheory.OrientedHeis.theta_smul x hf) (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
    X.m' X.fd' hIs.meas'.1 hIs.meas'.2 h
  simp only [LinearMap.toSpanSingleton_apply, one_smul] at key
  exact key

end GlobalTheory.SqTower

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralInjectiveSubspaceCompactOpenConstNeZero
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.integral_indicator_preimage_injective_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ],
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
    ∫ y, U.indicator (fun _ => c) (j y) ∂ν ≠ 0 := by
  intro F _ _ v κ _ N ν hν j hj c hc U hUo hUc h0
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hgc : Continuous g := IsModuleTopology.continuous_of_linearMap g
  set S : Set (Fin N → Fv F v) := j ⁻¹' U with hSdef
  have hSo : IsOpen S := hUo.preimage hjc
  have hSsub : S ⊆ g '' U := by
    intro y hy
    refine ⟨j y, hy, ?_⟩
    have := congrArg (fun f => f y) hg
    simpa using this
  have hfin : ν S < ⊤ := lt_of_le_of_lt (measure_mono hSsub) ((hUc.image hgc).measure_lt_top)
  have hpos : 0 < ν S := hSo.measure_pos ν ⟨0, by simp [hSdef, h0]⟩
  have heq : (fun y => U.indicator (fun _ => c) (j y)) = S.indicator (fun _ => c) := by
    funext y
    by_cases hy : j y ∈ U
    · have : y ∈ S := hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : y ∉ S := hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [heq, integral_indicator_const c hSo.measurableSet]
  refine smul_ne_zero ?_ hc
  rw [Measure.real]
  exact ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩
end

