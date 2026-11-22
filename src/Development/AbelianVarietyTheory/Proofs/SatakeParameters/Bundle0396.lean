import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0088
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.PureDegreeZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0393
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0390
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0389
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0830
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodConjugateNotMemFiltrationOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0850
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegrallyClosedSectionsOfSmoothComplex
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem isIntegrallyClosed_sections_of_smooth_complex :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) [Smooth s] (U : Z.Opens), IsAffineOpen U → genericPoint Z ∈ U → IsIntegrallyClosed Γ(Z, U) := by
  intro Z _ s hsm U hU hg
  have hs : (s.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth s hsm ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  letI : Algebra Γ(Sp ℂ, ⊤) Γ(Z, U) := (s.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.Smooth Γ(Sp ℂ, ⊤) Γ(Z, U) := hs
  let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  letI : Field Γ(Sp ℂ, ⊤) := (e.toMulEquiv.isField (Field.toIsField ℂ)).toField
  have : Nonempty U := ⟨⟨_, hg⟩⟩
  have : IsDomain Γ(Z, U) := inferInstance
  exact GlobalTheory.isIntegrallyClosed_of_smooth Γ(Sp ℂ, ⊤) Γ(Z, U)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonodromyVanishesWeilTwistIff
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open GlobalTheory.GalCut7

noncomputable section

namespace GlobalTheory.GalCut7.IwahoriTwist

open GlobalTheory.GalCut.IwaTwist GlobalTheory.GalCut.SsTwist Polynomial UpperTheory.V UpperTheory.V.Af

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : Formalism.ConjugateSelfDual.IsPlaceOver A w}

theorem monodromy_vanishes_weilTwist_iff (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : (x.lpTwist ξ hξ).mono0 ↔ x.mono0 := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff]
  rfl

theorem charPol_lpTwist_iff (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (g : Weil h) :
    (x.lpTwist ξ hξ).charPol g = (y.lpTwist ξ hξ).charPol g ↔ x.charPol g = y.charPol g := by
  rw [charPol_lpTwist, charPol_lpTwist]
  exact ⟨scaleRoots_cancel (Units.ne_zero _), fun e => by rw [e]⟩

end GlobalTheory.GalCut7.IwahoriTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RatioSpanCotangentChangeDenominator
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

theorem mem_of_algebraMap_mem_map_away {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (s : R)
    [IsLocalization.Away s S] {I m : Ideal R} (hm : m.IsMaximal) (hI : m ^ 2 ≤ I) (hs : s ∉ m) {x : R}
    (hx : algebraMap R S x ∈ I.map (algebraMap R S)) : x ∈ I := by
  obtain ⟨⟨y, t⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s) S).1 hx
  rw [← map_mul] at e
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers s) S).1 e
  have hw : ((c : R) * t) * x ∈ I := by
    have : (c : R) * y ∈ I := I.mul_mem_left _ y.2
    rw [← hc] at this
    convert this using 1; ring
  have hwm : (c : R) * t ∉ m := by
    obtain ⟨k, hk⟩ := c.2
    obtain ⟨l, hl⟩ := t.2
    rw [← hk, ← hl, ← pow_add]
    exact fun h => hs (hm.isPrime.mem_of_pow_mem _ h)
  obtain ⟨u, i, hi, h1⟩ := hm.exists_inv hwm
  have hi2 : i ^ 2 ∈ I := hI (Ideal.pow_mem_pow hi 2)
  have hx' : x = (u ^ 2 * ((c : R) * t) + 2 * u * i) * (((c : R) * t) * x) + x * i ^ 2 := by
    linear_combination (-x * (u * ((c : R) * t) + i + 1)) * h1
  rw [hx']
  exact I.add_mem (I.mul_mem_left _ hw) (I.mul_mem_left _ hi2)

theorem ker_le_map_ker_away {R S K : Type} [CommRing R] [CommRing S] [Field K] [Algebra R S] (s : R)
    [IsLocalization.Away s S] (evR : R →+* K) (evS : S →+* K) (h : ∀ x, evS (algebraMap R S x) = evR x) :
    RingHom.ker evS ≤ (RingHom.ker evR).map (algebraMap R S) := by
  intro w hw
  obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) w
  dsimp only at hw ⊢
  have hx : evR x = 0 := by
    have := congrArg evS (IsLocalization.mk'_spec S x t)
    rw [map_mul, RingHom.mem_ker.1 hw, zero_mul, h] at this
    exact this.symm
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)

theorem span_ratio_of_span_ratio (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N)
    (hι : IsClosedImmersion ι) (n : ℕ) (hn : 0 < n) (k : ℕ) (f : Fin k → MvPolynomial (Fin (N + 1)) ℂ)
    (a b : MvPolynomial (Fin (N + 1)) ℂ)
    (hf : ∀ j, f j ∈ GlobalTheory.ProjSpace.grading ℂ N n) (ha : a ∈ GlobalTheory.ProjSpace.grading ℂ N n)
    (hb : b ∈ GlobalTheory.ProjSpace.grading ℂ N n) (z : CxPts p (RingHom.id ℂ))
    (hza : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι a))
    (hzb : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι b))
    (h : RingHom.ker (CxPts.evHom hza) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) a (hf j) ha) ⊔
          RingHom.ker (CxPts.evHom hza) ^ 2) :
    RingHom.ker (CxPts.evHom hzb) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) b (hf j) hb) ⊔
          RingHom.ker (CxPts.evHom hzb) ^ 2 := by
  haveI := hι
  set 𝒜 := ProjSpace.grading ℂ N
  set D := Proj.basicOpen 𝒜 a ⊓ Proj.basicOpen 𝒜 b with hDdef
  set W : X.Opens := ι ⁻¹ᵁ D with hWdef
  have hWa : W ≤ fOpen ι a := fun x hx => hx.1
  have hWb : W ≤ fOpen ι b := fun x hx => hx.2
  have hzW : z ∈ CxPts.ptsIn p (RingHom.id ℂ) W :=
    CxPts.mem_ptsIn.2 ⟨CxPts.mem_ptsIn.1 hza, CxPts.mem_ptsIn.1 hzb⟩
  have hUa : IsAffineOpen (fOpen ι a) := (Proj.isAffineOpen_basicOpen 𝒜 a ha hn).preimage ι
  have hUb : IsAffineOpen (fOpen ι b) := (Proj.isAffineOpen_basicOpen 𝒜 b hb hn).preimage ι
  have hres : ∀ {c d : MvPolynomial (Fin (N + 1)) ℂ} (hc : c ∈ 𝒜 n) (hd : d ∈ 𝒜 n) (hW : W ≤ fOpen ι d)
      (hD : D ≤ Proj.basicOpen 𝒜 d),
      resG X hW (fRatio ι c d hc hd) = (ι.app D).hom (ProjFrac.frac 𝒜 D c d hc hd hD) := by
    intro c d hc hd hW hD
    have := congrArg (fun φ => φ.hom (ProjFrac.frac 𝒜 _ c d hc hd le_rfl)) (ι.naturality (homOfLE hD).op)
    simp only [CommRingCat.comp_apply] at this
    rw [← ProjFrac.resG_frac hD]
    exact this.symm

  have hratio : ∀ j, resG X hWa (fRatio ι (f j) a (hf j) ha) =
      resG X hWb (fRatio ι (f j) b (hf j) hb) * (ι.app D).hom (ProjFrac.frac 𝒜 D b a hb ha inf_le_left) := by
    intro j
    rw [hres _ _ hWa inf_le_left, hres _ _ hWb inf_le_right, ← map_mul]
    congr 1
    exact (ProjFrac.frac_mul_eq (by ring)).symm

  set sa := fRatio ι b a hb ha
  set sb := fRatio ι a b ha hb
  have eA : W = X.basicOpen sa := by
    rw [show sa = (ι.app _).hom (ProjFrac.frac 𝒜 _ b a hb ha le_rfl) from rfl]
    refine Eq.trans ?_ (Scheme.preimage_basicOpen ι _)
    rw [ProjFrac.basicOpen_frac]
  have eB : W = X.basicOpen sb := by
    rw [show sb = (ι.app _).hom (ProjFrac.frac 𝒜 _ a b ha hb le_rfl) from rfl]
    refine Eq.trans ?_ (Scheme.preimage_basicOpen ι _)
    rw [ProjFrac.basicOpen_frac]
    exact congrArg (fun U => ι ⁻¹ᵁ U) (inf_comm _ _)
  letI algA : Algebra Γ(X, fOpen ι a) Γ(X, W) := (resG X hWa).toAlgebra
  letI algB : Algebra Γ(X, fOpen ι b) Γ(X, W) := (resG X hWb).toAlgebra
  haveI locA : IsLocalization.Away sa Γ(X, W) := hUa.isLocalization_of_eq_basicOpen sa (homOfLE hWa) eA
  haveI locB : IsLocalization.Away sb Γ(X, W) := hUb.isLocalization_of_eq_basicOpen sb (homOfLE hWb) eB
  have evA : ∀ g, CxPts.evHom hzW (algebraMap Γ(X, fOpen ι a) Γ(X, W) g) = CxPts.evHom hza g := fun g => by
    change CxPts.evHom hzW (resG X hWa g) = _
    rw [← CxPts.ev_eq, ← CxPts.ev_eq]
    exact CxPts.ev_res hWa hzW g
  have evB : ∀ g, CxPts.evHom hzW (algebraMap Γ(X, fOpen ι b) Γ(X, W) g) = CxPts.evHom hzb g := fun g => by
    change CxPts.evHom hzW (resG X hWb g) = _
    rw [← CxPts.ev_eq, ← CxPts.ev_eq]
    exact CxPts.ev_res hWb hzW g
  have h1A := ker_le_map_ker_away sa _ _ evA
  have h1B := ker_le_map_ker_away sb _ _ evB
  have h2A : (RingHom.ker (CxPts.evHom hza)).map (algebraMap Γ(X, fOpen ι a) Γ(X, W)) ≤ RingHom.ker (CxPts.evHom hzW) :=
    Ideal.map_le_iff_le_comap.2 fun x hx => by
      rw [Ideal.mem_comap, RingHom.mem_ker, evA]; exact hx
  have h3 : RingHom.ker (CxPts.evHom hzW) ≤
      Ideal.span ((algebraMap Γ(X, fOpen ι a) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) a (hf j) ha) ⊔
        RingHom.ker (CxPts.evHom hzW) ^ 2 := by
    intro x hx
    have := Ideal.map_mono h (h1A hx)
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span] at this
    exact sup_le_sup le_rfl (Ideal.pow_right_mono h2A 2) this
  have h4 : Ideal.span ((algebraMap Γ(X, fOpen ι a) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) a (hf j) ha) ≤
      Ideal.span ((algebraMap Γ(X, fOpen ι b) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) b (hf j) hb) := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    change resG X hWa _ ∈ _
    rw [hratio j]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, ⟨j, rfl⟩, rfl⟩)

  have hsurj : Function.Surjective (CxPts.evHom hzb) := fun c =>
    ⟨ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (fOpen ι b) c, by rw [← CxPts.ev_eq]; exact CxPts.ev_algX hzb c⟩
  have hmax : (RingHom.ker (CxPts.evHom hzb)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have hs : sb ∉ RingHom.ker (CxPts.evHom hzb) := by
    rw [RingHom.mem_ker, ← CxPts.ev_eq]
    exact (CxPts.mem_ptsIn_basicOpen hzb sb).1 (eB ▸ hzW)
  intro g hg
  refine mem_of_algebraMap_mem_map_away (S := Γ(X, W)) sb hmax le_sup_right hs ?_
  have hgW : algebraMap Γ(X, fOpen ι b) Γ(X, W) g ∈ RingHom.ker (CxPts.evHom hzW) := by
    rw [RingHom.mem_ker, evB]; exact hg
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span]
  exact sup_le_sup h4 (Ideal.pow_right_mono h1B 2) (h3 hgW)

end GlobalTheory.EtProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLocalModelsOfSplitUnramifiedJoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem modelsOK_of_joints : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), (∀ μ, DV.Used D μ → JointsAt t μ) → (∀ u, ex.tw.e0 u D.what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _)) → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.ModelsOK D Gl ex.cmp Dx ex.tw := by
  intro hA hC D L hT Gi Gl Kc Dx cX ex t hJ h0 hS hk
  classical
  refine ⟨h0, fun μ u w hg => if h : DV.Used D μ ∧ D.what₂.places.resChar w ∉ Dx.Qp μ then
      ⟨Classical.choose (hJ μ h.1 u w hg h.2),
        chainAt (Classical.choose (Classical.choose_spec (Classical.choose_spec (hJ μ h.1 u w hg h.2)))) hT⟩
    else ⟨Gl.Lv u w hg, Gl.Ch u w hg⟩, ?_⟩
  intro μ hU u w hg hq
  have hP : DV.Used D μ ∧ D.what₂.places.resChar w ∉ Dx.Qp μ := ⟨hU, hq⟩
  dsimp only
  have key : ∀ x : (Σ Lv : Levels (Gl.Fl u w hg), Chain Lv),
      x = ⟨_, chainAt (Classical.choose (Classical.choose_spec (Classical.choose_spec (hJ μ hP.1 u w hg hP.2)))) hT⟩ →
      GlobalTheory.TwU.CmpLite D ex.cmp ex.tw u μ w hg x.2 ∧ GlobalTheory.TwU.SiteAdm D u w hg (Gl.Fl u w hg) x.1 x.2 := by
    rintro x rfl
    exact GlobalTheory.T.jointSite_chain_compared_carries_admittedSystem hA hC t
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hJ μ hP.1 u w hg hP.2))))).some
      hU hS hk
  exact key _ (dif_pos hP)

end GlobalTheory.TwV
end

