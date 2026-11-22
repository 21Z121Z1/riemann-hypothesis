import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Formalism.LocalToGlobal.HermitianColumns.Bundle0002
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0004

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.BesselUnipotentSubgroup
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsSplitSetIdem (D : D7) (e : AE D) : Prop :=
  ∃ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (ev : HeightOneSpectrum (𝓞 D.host.F) → AE D),
    (∀ v ∈ S, IsSplitIdem D (ev v) ∧ ∃ ε, IsPlaceIdem D v ε ∧ ev v + cA D (ev v) = algebraMap (AF D.host.F) (AE D) ε) ∧
    e = ∑ v ∈ S, ev v

structure IsDualFlag {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (f : Matrix (Fin B.rank) (Fin d.ρ) D.host.E) :
    Prop where
  iso : IsIsoSub B f
  pair : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * B.gram * f = 1
  perpA : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram * f = 0
  perpZ : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) f * B.gram).mulVec d.z = 0

def besselUnipotentSubgroup {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (f : Matrix (Fin B.rank) (Fin d.ρ) D.host.E) (eS : AE D) :
    Subgroup (GA D B) :=
  Subgroup.closure {g |
    SuppAt eS B g ∧
    (∀ k : Fin A.rank, eS • (subOne B g).mulVec (ratV fun i => frameMat B A ι i k) = 0) ∧
    (∀ k : Fin d.ρ, eS • (subOne B g).mulVec (ratV fun i => f i k) = 0) ∧
    (∀ k : Fin d.ρ, k.1 = 0 → eS • (subOne B g).mulVec (ratV fun i => d.e i k) = 0) ∧
    (d.ρ = 0 → eS • (subOne B g).mulVec (ratV d.z) = 0) ∧
    ∀ x : Fin B.rank → D.host.E, ∃ a : Fin A.rank → AE D,
      eS • (subOne B g).mulVec (ratV x) = ((frameMat B A ι).map (incA D)).mulVec a}

structure BesselCompatibility' (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (B : BesselTied D X T Wl) where

  eS : D.what₂.Word → AE D
  eS_split : ∀ u, IsSplitSetIdem D (eS u)

  f : ∀ u (ho : Odd ((D.sp.Y 0).rank - (D.sp.X 0).rank)),
    Matrix (Fin (D.sp.Y 0).rank) (Fin (B.dat _ _ _ ho (X.pos1 u)).ρ) D.host.E
  f_dual : ∀ u ho, IsDualFlag (B.dat _ _ _ ho (X.pos1 u)) (f u ho)

  mu1 : ∀ u ho, Measure (besselUnipotentSubgroup (B.dat _ _ _ ho (X.pos1 u)) (f u ho) (eS u))
  mu_one_isHaarMeasure : ∀ u ho, (mu1 u ho).IsHaarMeasure

  bper1 : ∀ u (ho : Odd ((D.sp.Y 0).rank - (D.sp.X 0).rank)), (D.sp.X 0).rank ≤ (D.sp.Y 0).rank → (D.sp.X 0).SigOK →
    HSpace.IsIsomEmb (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) → ∀ (sF : X.FJd (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0)),
    ∀ μ 𝓕, IsVolPair D (D.sp.X 0) μ 𝓕 →
    ∀ (μN : Measure (NFlag (D.sp.Y 0) (B.dat _ _ _ ho (X.pos1 u)).e)) (𝓕N : Set (NFlag (D.sp.Y 0) (B.dat _ _ _ ho (X.pos1 u)).e)),
      μN.IsHaarMeasure → IsFundamentalDomain (NFlagQ (D.sp.Y 0) (B.dat _ _ _ ho (X.pos1 u)).e) 𝓕N μN → μN 𝓕N = 1 →
    ∀ s : GA D (D.sp.X 0) → GA D (D.sp.Y 0), (∀ h, EmbRel (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (s h) h) →
    ∀ (φ : X.AF (D.sp.X 0)) (F : X.cusp (D.sp.Y 0)), IsAniso (D.sp.X 0) ∨ φ ∈ X.cusp (D.sp.X 0) →
      X.Bper (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) (X.pos1 u) sF φ F =
        ∫ g, ((B.besC _ _ _ (X.pos1 u) * T.petC (D.sp.X 0) : ℝ) : ℂ) *
          ∫ h in 𝓕, ∫ n in 𝓕N, star (T.ev (D.sp.X 0) φ h) *
            T.ev (D.sp.Y 0) (F : X.AF (D.sp.Y 0))
              ((n : GA D (D.sp.Y 0)) * s h * (g : GA D (D.sp.Y 0)) * ((B.dat _ _ _ ho (X.pos1 u)).y : GA D (D.sp.Y 0))) *
            star (besChar Wl.ψ (B.dat _ _ _ ho (X.pos1 u)) (n : GA D (D.sp.Y 0))) ∂μN ∂μ ∂(mu1 u ho)

end Formalism.L2.Theta

end
end

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.Joints
section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Theta

theorem VolTieG.hermVolTied {D : D7} (h : VolTieG D) : Formalism.L2.Herm.VolumeCompatible D := by
  intro W P Q hs hsig μ hμ 𝓕 h𝓕
  exact ((h.volTie W P Q hs hsig).2 μ hμ).2 𝓕 h𝓕

end Formalism.L2.Theta

end
end

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.TiedDef
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : ThetaX D}

structure ThetaTiedDef (T : ThetaTied D X) : Prop where

  ev_def : ∀ V : HSp D, V.SigOK → V.IsDefinite → Set.range (T.ev V) = {φ | IsAutFunDef V φ}

  typ : ∀ V : HSp D, V.SigOK → V.IsDefinite → ∀ P : D.what₂.Tau → SPar,
    (∀ τ, GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (P τ)) →
    X.typ V P = ⨅ τ, isoDef (gramAt D V τ) (X.actR V τ) (P τ)

def AutFunDefIffSm (D : D7) : Prop :=
  ∀ θ, IsInfFam (D := D) θ → ∀ V : HSp D, V.SigOK → V.IsDefinite → ∀ φ, IsAutFunDef V φ ↔ IsAutFunSm θ V φ

def IsoDefIffTypeAt (T : ThetaTied D X) : Prop :=
  ∀ θ, IsInfFam (D := D) θ → ∀ V : HSp D, V.SigOK → V.IsDefinite → ∀ P : D.what₂.Tau → SPar,
    (∀ τ, GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (P τ)) → ∀ F : X.AF V,
      F ∈ (⨅ τ, isoDef (gramAt D V τ) (X.actR V τ) (P τ)) ↔ ∀ τ, IsTypeAt θ V τ (P τ) (T.ev V F)

theorem defOneIndef {V : HSp D} (hd : V.IsDefinite) : ∀ τ τ' : D.what₂.Tau, τ ≠ τ' →
    (V.sig (tauE D τ)).1 = 0 ∨ (V.sig (tauE D τ)).2 = 0 ∨ (V.sig (tauE D τ')).1 = 0 ∨ (V.sig (tauE D τ')).2 = 0 := by
  intro τ _ _
  rcases hd (tauE D τ) with h | h
  · exact Or.inr (Or.inl (by rw [h]))
  · exact Or.inl (by rw [h])

theorem sParGap_of_isDefinite {V : HSp D} (hd : V.IsDefinite) (P : D.what₂.Tau → SPar) :
    ∀ τ, SParGap V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (P τ) := by
  intro τ
  rcases hd (tauE D τ) with h | h
  · exact Or.inr (Or.inl (by rw [h]))
  · exact Or.inl (by rw [h])

theorem ThetaTiedDef.of_iff {T : ThetaTied D X} (sm : ThetaSmoothnessCondition T) (ty : TypTied T) (h1 : AutFunDefIffSm D)
    (h2 : IsoDefIffTypeAt T) : ThetaTiedDef T where
  ev_def := by
    intro V hs hd
    obtain ⟨θ, hθ⟩ := sm.1
    rw [sm.2 θ hθ V hs]
    ext φ
    exact (h1 θ hθ V hs hd φ).symm
  typ := by
    intro V hs hd P hP
    obtain ⟨θ, hθ⟩ := ty.1
    ext F
    rw [ty.2 θ hθ V hs P hP (sParGap_of_isDefinite hd P) F]
    exact (h2 θ hθ V hs hd P hP F).symm

theorem ThetaTiedDef.autFunDefIffSm {T : ThetaTied D X} (h : ThetaTiedDef T) (sm : ThetaSmoothnessCondition T) : AutFunDefIffSm D := by
  intro θ hθ V hs hd φ
  have e : {φ | IsAutFunDef V φ} = {φ | IsAutFunSm θ V φ} := by rw [← h.ev_def V hs hd, sm.2 θ hθ V hs]
  exact Set.ext_iff.1 e φ

theorem ThetaTiedDef.isoDefIffTypeAt {T : ThetaTied D X} (h : ThetaTiedDef T) (ty : TypTied T) : IsoDefIffTypeAt T := by
  intro θ hθ V hs hd P hP F
  rw [← h.typ V hs hd P hP]
  exact ty.2 θ hθ V hs P hP (sParGap_of_isDefinite hd P) F

end Formalism.L2.Theta

end
end

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.TiedLocW
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def conjId (D : D7) : (AE D)ˣ →* (AE D)ˣ := Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

def IsHeckeCharF (D : D7) (χ : (AF D.host.F)ˣ →* Circle) : Prop :=
  Continuous χ ∧ ∀ a : D.host.Fˣ, χ (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) = 1

structure ConjDat {D : D7} (V : HSp D) where
  P : Matrix (Fin V.rank) (Fin V.rank) D.host.E
  rel : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * V.gram * P =
    V.gram.map (D.sp.cm.sig : D.host.E →+* D.host.E)
  aut : GA D V ≃* GA D V
  aut_mt : ∀ g, HMul.hMul (mt V (aut g)) (P.map (incA D)) = HMul.hMul (P.map (incA D)) (cM (mt V g))

structure LocWTied (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L : Formalism.MainNotions.KudlaSiegelWeil.LocW D X) where

  sR : L.sR = true

  eG : ∀ V, L.G V ≃* GA D V
  eG_meas : ∀ V, Measurable (eG V)

  gf : ∀ V g, g ∈ L.GF V ↔ eG V g ∈ GQ V

  muC : HSp D → ℝ
  muC_pos : ∀ V, 0 < muC V

  mu : ∀ V : HSp D, V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 →
    Measure.map (eG V) (L.μG V) = ENNReal.ofReal (muC V) • μ

  cj : ∀ V : HSp D, ConjDat V

  om : ∀ (V W : HSp D) χ χ' g h, V.rank ≠ W.rank → L.om V W χ χ' (g, h) =
    if V.rank < W.rank then Wl.om V W χ χ' ((cj V).aut (eG V g), eG W h)
    else Wl.om V W χ χ' (eG V g, (cj W).aut (eG W h))

  thF : ∀ V W Φ, L.thF V W Φ = Wl.evS V W Φ 0

  eChrF : L.ChrF →* ((AF D.host.F)ˣ →* Circle)
  eChrF_inj : Function.Injective eChrF
  eChrF_mem : ∀ χ, IsHeckeCharF D (eChrF χ)

  res : ∀ χ a, eChrF (L.res χ) a = T.eChr χ (idF D a)

  eta : IsEta D (eChrF L.eta)

  cc : ∀ χ x, T.eChr (L.cc χ) x = T.eChr χ (conjId D x)

def LocalWhittakerKFiniteCompatibility {D : D7} {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T} {L : Formalism.MainNotions.KudlaSiegelWeil.LocW D X}
    (h : LocWTied D X T Wl L) (Kf : KfinTied Wl) : Prop :=
  AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, V.SigOK →
    (∀ g, g ∈ L.Gk V ↔ ∃ a ∈ GfC V, ∃ k, IsKinf θ V (Kf.cpt V) k ∧ h.eG V g = a * k) ∧
    ∀ k, IsKinf θ V (Kf.cpt V) k → IsKinf θ V (Kf.cpt V) ((h.cj V).aut k)

def CjOfBas {D : D7} {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T} {L : Formalism.MainNotions.KudlaSiegelWeil.LocW D X}
    (h : LocWTied D X T Wl L) (Kf : KfinTied Wl) : Prop :=
  ∀ V : HSp D, V.SigOK → (h.cj V).P * (Kf.bas V).map (D.sp.cm.sig : D.host.E →+* D.host.E) = Kf.bas V

theorem LocWTied.ePlus {D : D7} {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T} {L : Formalism.MainNotions.KudlaSiegelWeil.LocW D X}
    (h : LocWTied D X T Wl L) (τ : D.what₂.Tau) : Formalism.MainNotions.KudlaSiegelWeil.ePlus L τ :=
  ⟨fun _ => h.sR, fun _ => xi_zero_im_pos D τ⟩

end Formalism.L2.Theta

end
end

