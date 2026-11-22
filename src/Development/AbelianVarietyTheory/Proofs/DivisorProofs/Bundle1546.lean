import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MemSpanCentreTranslates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
import GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdeleTopology

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionValuationAtFinitePlaceEqSubDet
section
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt

theorem vV_algebraMap_of_isUnit (T : CDVR) {u : T.V} (hu : IsUnit u) : vV T.V (algebraMap T.V T.Fr u) = 0 := by
  have : valV T.V (algebraMap T.V T.Fr u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal u).1 h hu
  simp [vV, this]

theorem rho_vw_eq_vAdd_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ w, s.rho_vw w = (vAdd w b : ℝ) - (vAdd w (P.B w τ.1).det : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s b hb hev w
  obtain ⟨v, hv⟩ := s.hasPts.2 w
  have hval := s.val_eq hv
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  have hval' : nval T.V e (evR Xo c s.sig y.1) = ((flDefect_vw Dw c τ w + s.rho_vw w : ℝ) : EReal) := hval
  have hδ : flDefect_vw Dw c τ w = 0 := by simp [flDefect_vw, hD.q]
  rw [hδ, zero_add] at hval'
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F T.Fr
    (Algebra.ofId c.F T.Fr) P.y₀
  obtain ⟨ha, hB, hloc⟩ := P.loc w
  have hx : y.1.x = z.x := (P.only T.Fr y.1 hy.2).trans hz.1.symm
  obtain ⟨Y, u, hY, hch⟩ := hloc T io e ho y.1 z y.2.2 hz hx
  have hdet : ∀ τ', ((P.B w τ').map io * (Y τ').map (algebraMap T.V T.Fr)).det =
      io (P.B w τ').det * algebraMap T.V T.Fr (Y τ').det := fun τ' => by
    rw [Matrix.det_mul, RingHom.map_det, RingHom.map_det]; rfl
  have hYne : ∀ τ', algebraMap T.V T.Fr (Y τ').det ≠ 0 := fun τ' => ((hY τ').map _).ne_zero
  have hBne : ∀ τ', io (P.B w τ').det ≠ 0 := fun τ' => (map_ne_zero io).2 (hB τ')
  have key := hev T.Fr z y.1 (fun τ' => (P.B w τ').map io * (Y τ').map (algebraMap T.V T.Fr)) _
    (fun τ' => by rw [hdet]; exact (mul_ne_zero (hBne τ') (hYne τ')).isUnit)
    (mul_ne_zero ((map_ne_zero io).2 ha) (u.isUnit.map _).ne_zero).isUnit hz hch
  rw [hdet] at key
  have key' : evR Xo c s.sig y.1 * (io (P.B w τ.1).det * algebraMap T.V T.Fr (Y τ.1).det) = io b := key
  have hbne : io b ≠ 0 := (map_ne_zero io).2 hb
  have h0 : evR Xo c s.sig y.1 ≠ 0 := left_ne_zero_of_mul (key' ▸ hbne)
  have h1 := congrArg (vV T.V) key'
  rw [vV_mul h0 (mul_ne_zero (hBne _) (hYne _)), vV_mul (hBne _) (hYne _), vV_algebraMap_of_isUnit T (hY _),
    ho.2, ho.2] at h1
  rw [nval_of_ne h0, EReal.coe_eq_coe_iff] at hval'
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have h2 := congrArg (Int.cast : ℤ → ℝ) h1
  push_cast at h2
  rw [← hval', div_eq_iff he]
  show _ = ((vLa w b : ℝ) - (vLa w (P.B w τ.1).det : ℝ)) * e
  linarith

end GlobalTheory.DefPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumLinePlacewiseSignatures
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD GlobalTheory.VacLn

namespace GlobalTheory.HoweD

theorem vacD_ne_zero {ι : Type} [Fintype ι] {P Q R S : ι → ℕ} :
    (PiTensorProduct.tprod ℂ fun w : ι => (1 : Pol (P w) (Q w) (R w) (S w))) ≠ 0 := by
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap
    fun w => (MvPolynomial.aeval (R := ℂ) (S₁ := ℂ) (σ := Ln (P w) (Q w) (R w) (S w)) fun _ => 0).toLinearMap)) h
  simp at this

theorem vacLineD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → ∀ (f₀ : SInf F κ) (ε : InfinitePlace F → ℤˣ),
    (∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) →
      ∀ f f' : SInf F κ, SD (fun t => d.rho ψ (realAd F t • u)) f₀ f → SD (fun t => d.rho ψ (realAd F t • u')) f₀ f' →
        f' = Complex.I • f) →
    ∃ z : ℂ, f₀ = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hStd hFr hΦ f₀ ε hyp
  have hD : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  obtain ⟨D, hDu⟩ := hD F E σ α β κ ψ JA JB d hStd
  obtain ⟨J, e, e', hJ, he, hJe, he1, he2, hy⟩ := GlobalTheory.T.exists_archimedeanPhaseSpace_complexStructure_signatures F E σ α β κ P Q R S τ JA JB d a b A C ε hCM hFr
  have hDx : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x = fderiv ℝ f x (coord d u).1 -
      2 * Real.pi * Complex.I * (trPair F κ x (coord d u).2 : ℝ) * f x := fun u hu f x => (hDu u hu f).2 x
  have hf : ∀ y x, fderiv ℝ f₀ x (J (y - (2 : ℝ) • e y)).1 - 2 * Real.pi * Complex.I *
      (trPair F κ x (J (y - (2 : ℝ) • e y)).2 : ℝ) * f₀ x =
      Complex.I * (fderiv ℝ f₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * f₀ x) := by
    intro y x
    obtain ⟨u, u', u₁, c, hu, hu', -, hc, hc', -, h0, h', -⟩ := hy y
    have key := hyp u u' hu hu' c hc hc' (D u f₀) (D u' f₀) (hDu u hu f₀).1 (hDu u' hu' f₀).1
    have := congrArg (fun g : SInf F κ => g x) key
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u' hu', h0, h'] at this
    exact this
  set g₀ := Φ (PiTensorProduct.tprod ℂ fun _ => 1) with hg₀
  have hg0 : g₀ ≠ 0 := fun h => vacD_ne_zero (hΦ.1 (h.trans (map_zero Φ).symm))
  have hg : ∀ y x, fderiv ℝ g₀ x (J y).1 - 2 * Real.pi * Complex.I * (trPair F κ x (J y).2 : ℝ) * g₀ x =
      Complex.I * (fderiv ℝ g₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * g₀ x) := by
    intro y x
    obtain ⟨u, -, u₁, c, hu, -, hu₁, hc, -, hc₁, h0, -, h1⟩ := hy y
    have e0 := GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators (hDu u hu g₀).1 (hΦ.2 u hu c hc _)
    have e1 := GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators (hDu u₁ hu₁ g₀).1 (hΦ.2 u₁ hu₁ _ hc₁ _)
    rw [GlobalTheory.T.fock_vacuum_pi_tensor_heisenberg_factorwise_signature, map_smul, ← e0] at e1
    have := congrArg (fun g : SInf F κ => g x) e1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u₁ hu₁, h0, h1] at this
    exact this
  obtain ⟨z, hz⟩ := GlobalTheory.T.schwartz_complexStructure_vacuum_solution_eq_smul (trPair F κ) (fun y h => GlobalTheory.T.archimedeanTracePairingBilinear_nondegenerate y h) J e e' hJ he hJe he1 he2 f₀ g₀ hg0 hg hf
  exact ⟨z, hz⟩

end GlobalTheory.HoweD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoefficientFamilyPullbackFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.Tors.CoefPull

open GlobalTheory.FieldBaseChange GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic GlobalTheory.UT.EvalZero

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {E F : Type} [Field F] [Algebra (FractionRing R) F]
  [Field E] [Algebra (FractionRing R) E] [Algebra E F] [IsScalarTower (FractionRing R) E F]

theorem cst_map (z : (TF (R := R) F).left) (a : E) :
    cst (R := R) F z (algebraMap E F a) =
      ((baseMap (R := R) E F).left.stalkMap z).hom (cst (R := R) E ((baseMap (R := R) E F).left z) a) := by
  refine Eq.trans ?_ (gs_comp_stalkMap (𝟙 _) (baseMap (R := R) E F).left z ⊤ trivial _)
  rw [Category.comp_id]
  refine Eq.trans ?_ ((gs_pull (𝟙 _) (baseMap (R := R) E F).left z ⊤ trivial _).trans (by rw [Category.id_comp]))
  refine congrArg (gs (𝟙 _) z ⊤) ?_
  exact congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap E F)))

theorem coef_famPull (hf : (algebraMap E F).comp (algebraMap (FractionRing R) E) = algebraMap (FractionRing R) F)
    (hG : GlobalFnsSt) (k : ℕ) (s : Fam D E k) (g : GtPtF D E) (w : Frm D E k g.b)
    (w' : Frm D F k (gtExt D (algebraMap E F) hf g).b) (hw : w.IsGen)
    (hv : ∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (spMap (algebraMap E F)) z J) (χ : D.X) :
    coef (famPull D E F hG k s) (gtExt D (algebraMap E F) hf g) w' χ = algebraMap E F (coef s g w χ) := by
  refine coef_eq fun z J hJ => ?_
  let p := baseMap (R := R) E F
  have hJ' : Good D.P.L (p.left z) (fun ψ => J (p.left ≫ ψ)) := fun ψ => hJ (p.left ≫ ψ)
  have a := congrArg (p.left.stalkMap z).hom (isCoef_coef g hw χ s (p.left z) _ hJ')
  rw [map_mul, map_mul, map_mul, map_pow] at a
  have hb : (gtExt D (algebraMap E F) hf g).b = p ≫ g.b := gtExt_b _ hf g
  have e : lift (𝟙 (TF (R := R) F)) (gtExt D (algebraMap E F) hf g).b ≫ famMap D E F = p ≫ lift (𝟙 _) g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, famMap_fst, lift_fst_assoc, Category.assoc, lift_fst, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, lift_snd, ← hb]
      exact (congrArg _ (famMap_snd D E F)).trans (lift_snd _ _)
  have e' : (lift (𝟙 (TF (R := R) F)) (gtExt D (algebraMap E F) hf g).b).left ≫ (famMap D E F).left =
      p.left ≫ (lift (𝟙 _) g.b).left := congrArg (fun q => q.left) e
  refine (congrArg₂ (· * ·) (cst_map z _) (congrArg (· ^ k) ?_)).trans (a.trans
    (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_).symm)
  · exact val_comp_map (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig p.left
      (TF (R := R) E).hom _ (Over.w p) z hJ
  · refine (sval_pullOver _ _ _ _ hJ).trans ?_
    refine Eq.trans (by rw [e']) ?_
    exact (values_natural _ _ _ _ D.P.L _ _ _ _ p.left z J hJ).2.1 (s.s χ)
  · exact (congrArg Units.val (gtExt_val _ hf g χ hJ)).trans (val_comp_map _ p.left (𝟙 _) _ (Category.comp_id _) z hJ)
  · exact (congrArg Units.val (hv z J hJ)).trans (val_comp_map _ p.left (𝟙 _) _ (Category.comp_id _) z hJ)

theorem coef_famPull_frac : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (hG : GlobalFnsSt) (k : ℕ) (s : Fam D (FractionRing R) k) (g : GtPtF D (FractionRing R)) (w : Frm D (FractionRing R) k g.b) (w' : Frm D F k (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b), w.IsGen → w'.IsGen → (∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (spMap (algebraMap (FractionRing R) F)) z J) → ∀ χ : D.X, coef (GlobalTheory.FieldBaseChange.famPull D (FractionRing R) F hG k s) (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) w' χ = algebraMap (FractionRing R) F (coef s g w χ) :=
  fun _ _ _ _ _ _ _ hG k s g w w' hw _ hv χ => coef_famPull _ hG k s g w w' hw hv χ

end GlobalTheory.Poinc.Tors.CoefPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliWithSymplecticLevelRepresentab
section
noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

def IsLevelStructureOfLevel {D : Datum F} {p N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) (N₁ : ℕ)
    (α : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  (∀ a c, α (a + c) = α a * α c) ∧ (∀ a, α (N₁ • a) = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      (∀ a, toUnit (Over.mk x) ≫ α a = 1 ↔ ∃ b, a = N₁ • b) ∧
      (∀ g : Over.mk x ⟶ o.A, g ^ N₁ = 1 → ∃ a, toUnit _ ≫ α a = g) ∧
      ∃ z : kˣ, IsPrimitiveRoot z N₁ ∧
        ∀ a b, Out.WeilIs o.A o.PP.L N₁ (toUnit (Over.mk x) ≫ α a) (toUnit _ ≫ α b) (unitOn (z ^ D.EF a b))

def LevelStructurePullback {D : Datum F} {p N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp (D.OEp p)} {s' : S' ⟶ Sp (D.OEp p)}
    {o' : Obj D p N s'} {o : Obj D p N s} {f : S' ⟶ S} (m : ObjMap o' o f) (α' : D.La → (𝟙_ (Over S') ⟶ o'.A))
    (α : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  ∀ a, (α' a).left ≫ m.φ = f ≫ (α a).left

def HasLevelStructureOfLevel {D : Datum F} {p N : ℕ} {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp (D.OEp p)} (o₁ : Obj D p N s₁) (N₁ : ℕ)
    (α₁ : D.La → (𝟙_ (Over X₁) ⟶ o₁.A)) : Prop :=
  ∀ (S : Scheme.{0}) (s : S ⟶ Sp (D.OEp p)) (o : Obj D p N s) (α : D.La → (𝟙_ (Over S) ⟶ o.A)), IsLevelStructureOfLevel o N₁ α →
    ∃! f : S ⟶ X₁, f ≫ s₁ = s ∧ ∃ m : ObjMap o o₁ f, LevelStructurePullback m α α₁

abbrev LaMod (D : Datum F) (N₁ : ℕ) : Type := ZMod N₁ ⊗[ℤ] D.La

abbrev EFMod (D : Datum F) (N₁ : ℕ) : LinearMap.BilinForm (ZMod N₁) (LaMod D N₁) := D.EF.baseChange (ZMod N₁)

def toLaMod (D : Datum F) (N₁ : ℕ) : D.La →+ LaMod D N₁ :=
  (TensorProduct.mk ℤ (ZMod N₁) D.La 1).toAddMonoidHom

theorem toLaMod_apply (D : Datum F) (N₁ : ℕ) (a : D.La) : toLaMod D N₁ a = (1 : ZMod N₁) ⊗ₜ a := rfl

theorem toLaMod_surjective (D : Datum F) (N₁ : ℕ) : Function.Surjective (toLaMod D N₁) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul r a =>
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective r
    refine ⟨n • a, ?_⟩
    rw [toLaMod_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul, _root_.mul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

def simGrp (D : Datum F) (N₁ : ℕ) : Subgroup (LaMod D N₁ ≃ₗ[ZMod N₁] LaMod D N₁) where
  carrier := {g | ∃ m : (ZMod N₁)ˣ, ∀ x y, EFMod D N₁ (g x) (g y) = m * EFMod D N₁ x y}
  one_mem' := ⟨1, fun x y => by simp⟩
  mul_mem' := by
    rintro g h ⟨m, hm⟩ ⟨m', hm'⟩
    refine ⟨m * m', fun x y => ?_⟩
    change EFMod D N₁ (g (h x)) (g (h y)) = _
    rw [hm, hm', Units.val_mul, _root_.mul_assoc]
  inv_mem' := by
    rintro g ⟨m, hm⟩
    refine ⟨m⁻¹, fun x y => ?_⟩
    have h := hm (g⁻¹ x) (g⁻¹ y)
    have e : ∀ z, g (g⁻¹ z) = z := fun z => by
      change (g * g⁻¹) z = z
      rw [mul_inv_cancel]; rfl
    rw [e, e] at h
    rw [h, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]

def twist (D : Datum F) (N₁ : ℕ) {T : Type} (g : simGrp D N₁) (α : D.La → T) : D.La → T :=
  fun a => α (Function.surjInv (toLaMod_surjective D N₁) ((g : LaMod D N₁ ≃ₗ[ZMod N₁] LaMod D N₁) (toLaMod D N₁ a)))

end GlobalTheory.UPel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HatCPhiHat
section
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts GlobalTheory.AdTh
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdTh

theorem unr_of {D : D7} {χ : (AE D)ˣ →* Circle} (h : UnramEverywhere D χ) {v ε} (hε : IsPlaceIdem D v ε) : UnramAt ε χ := by
  intro x hx h1 h2
  refine h x ?_ h1 h2
  obtain ⟨α, rfl, -⟩ := hε
  have h3 := congrArg (infPart D) hx
  have h4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    have e2 : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
    have e3 := Algebra.TensorProduct.map_tmul (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α) 1
    rw [e2, TensorProduct.zero_tmul] at e3
    exact e3
  rw [map_mul, h4, zero_mul, map_sub, map_one] at h3
  exact (sub_eq_zero.1 h3.symm)

theorem isPair_pow (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (V W : HSp D) (h1 : V.gram = 1) (h2 : Even V.rank) (h3 : V.SigOK) (h4 : W.SigOK) (η) (hη : IsEtaTilde D η) :
    ∃ om, IsPair ψ θ V W (η ^ V.rank) (η ^ W.rank) om := by
  have hH : ∀ n : ℕ, IsHeckeChar D (η ^ n) := fun n =>
    ⟨by
      have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by funext x; simp
      rw [this]; exact hη.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, hη.1.2 x, one_pow]⟩
  have hR : ∀ n : ℕ, ResEta D (η ^ n) n := fun n =>
    ⟨hη.2.2.1.1, fun e he a => by rw [MonoidHom.pow_apply, hη.2.2.1.2 e he a, pow_one]⟩
  have hE : ∀ (n : ℕ) τ, HasInfExp D (η ^ n) τ ((n : ℚ) / 2) := fun n τ => by
    obtain ⟨m, hm, ha, hb⟩ := hη.2.2.2 τ
    have hm1 : m = 1 := by
      have : (m : ℚ) = 1 := by rw [hm]; norm_num
      exact_mod_cast this
    subst hm1
    refine ⟨n, by push_cast; ring, ha, fun θ' hθ' x hx hx' => ?_⟩
    rw [MonoidHom.pow_apply, Circle.coe_pow, hb θ' hθ' x hx hx', zpow_one, zpow_natCast]
  have hU : ∀ n : ℕ, UnramEverywhere D (η ^ n) := fun n x a b c => by
    rw [MonoidHom.pow_apply, hη.2.1 x a b c, one_pow]
  obtain ⟨om, hom⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hψ V W _ _ ⟨η, hη⟩ (hH _) (hH _) (hR _) (hR _)
  refine ⟨om, hom, hθ, h1, h2, h3, h4, fun τ => ?_, fun τ => ⟨0, by simpa using hE W.rank τ⟩,
    fun v ε h => ⟨unr_of (hU _) h.1, unr_of (hU _) h.1⟩, ⟨η, hη⟩⟩
  obtain ⟨a, ha⟩ := h2
  refine ⟨a, ?_⟩
  have := hE V.rank τ
  rwa [show ((V.rank : ℚ) / 2) = ((a : ℤ) : ℚ) by rw [ha]; push_cast; ring] at this

theorem isPair_rec (D : D7) (i : Fin D.R.m) (hV : VStd D i) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (η) (hη : IsEtaTilde D η) :
    0 < (Vc D i).rank ∧ 0 < (Wc D i).rank ∧ ∃ θ χV χW om, IsPair ψ θ (Vc D i) (Wc D i) χV χW om := by
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  obtain ⟨θ, hθ⟩ := hψ.2.1
  refine ⟨hr.trans_le (r_le_V i), hr.trans_le (r_le_rank_Wc i), θ, _, _,
    isPair_pow D ψ hψ θ hθ _ _ hV.1 ?_ (D.sp.V_sig _) (D.sp.W_sig _) η hη⟩
  rw [D.sp.V_rank _ (Nat.le_add_left _ _) i.2]
  exact (kapDom D).2

theorem hatC_phiHat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {n : ℕ} (φ : (Fin n → LevQc Dw l) → c.F) (hf : Finite (Fin n → LevQc Dw l)) (q : Fin n → LevQ Dw l) :
    hatC l (fun x => (φ x : ℂ)) q = ((phiHat c φ q : c.F) : ℂ) := by
  have hz : ((zetaM c : c.F) : ℂ) = Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) := by
    have hM : (l.M : ℂ) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
    have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by rintro rfl; simp at hk; exact hM' hk : k ≠ 0)
    simp only [zetaM, SubmonoidClass.coe_pow, zeta]
    rw [← Complex.exp_nat_mul, hk, Nat.mul_div_cancel_left _ (by have := l.three_le; omega)]
    congr 1; push_cast; field_simp
  have := Fintype.ofFinite (Fin n → LevQc Dw l)
  unfold hatC phiHat
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← hz]
  show _ = c.F.val _
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_zpow₀]
  rfl

theorem markAd_one {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (W : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) : MarkAd l W rfl ι 1 ι := by
  intro a _
  refine ⟨0, zero_mem _, ?_⟩
  rw [map_one, nsmul_zero, Units.val_one, Matrix.one_mulVec]
  exact sub_self _

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharTrivialUniformizers
section
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.IdTorus GlobalTheory.GLTwoHecke
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut (IsMaxCpt)
open GlobalTheory.StdPar

noncomputable section

namespace GlobalTheory.HeckeUnifApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Inf

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def swapL : (InfiniteAdeleRing F ⊗[F] E) →ₗ[InfiniteAdeleRing F] (E ⊗[F] InfiniteAdeleRing F) where
  toFun := Algebra.TensorProduct.comm F (InfiniteAdeleRing F) E
  map_add' := map_add _
  map_smul' c t := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1

def swapR : (E ⊗[F] InfiniteAdeleRing F) →ₗ[InfiniteAdeleRing F] (InfiniteAdeleRing F ⊗[F] E) where
  toFun := Algebra.TensorProduct.comm F E (InfiniteAdeleRing F)
  map_add' := map_add _
  map_smul' c t := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1

theorem exists_infinite_equiv :
    ∃ j : (Ainf F ⊗[F] E) ≃+* InfiniteAdeleRing E, Continuous j ∧ Continuous j.symm ∧
      ∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x := by
  letI tB : TopologicalSpace (E ⊗[F] InfiniteAdeleRing F) := moduleTopology (InfiniteAdeleRing F) _
  haveI : IsModuleTopology (InfiniteAdeleRing F) (E ⊗[F] InfiniteAdeleRing F) := ⟨rfl⟩
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) (E ⊗[F] InfiniteAdeleRing F)
  haveI := IsModuleTopology.toContinuousSMul (InfiniteAdeleRing F) (E ⊗[F] InfiniteAdeleRing F)
  haveI := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI := IsModuleTopology.toContinuousSMul (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  have hL : Continuous (swapL (F := F) (E := E)) := IsModuleTopology.continuous_of_linearMap _
  have hR : Continuous (swapR (F := F) (E := E)) := IsModuleTopology.continuous_of_linearMap _
  let h := GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingHomeomorph (K := F) (L := E)
  refine ⟨(Algebra.TensorProduct.comm F (InfiniteAdeleRing F) E).toRingEquiv.trans
    (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)).toRingEquiv, ?_, ?_, ?_⟩
  · exact h.continuous.comp hL
  · exact hR.comp h.symm.continuous
  · intro x
    change GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv
      (Algebra.TensorProduct.comm F (InfiniteAdeleRing F) E ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x)) = _
    rw [Algebra.TensorProduct.comm_tmul, GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one,
      mul_one]

end Inf

open GlobalTheory.LFun in

theorem exists_tensor_adele_equiv :
    ∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
      Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
      ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z)) := by
  obtain ⟨j, hjc, hjc', hj⟩ := exists_infinite_equiv (F := F) (E := E)
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨s.trans (j.prodCongr (finAdEquiv F E)), j, (hjc.prodMap GlobalTheory.DefU.ClassFin.continuous_finAdEquiv).comp hsc,
    hsc'.comp (hjc'.prodMap continuous_finAdEquiv_symm), hj,
    fun z => Prod.ext (congrArg j (hs z).1) (congrArg (finAdEquiv F E) (hs z).2)⟩

open GlobalTheory.LFun in

theorem exists_hchar (χ : (AF F ⊗[F] E)ˣ →* Circle) (hχ : IsHecke F E χ) :
    ∃ (H : Formalism.L2.Host.HChar E) (u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ),
      (∀ y, H.1 y = Circle.toUnits (χ (u y))) ∧ Function.Surjective u ∧
      ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x := by
  obtain ⟨Φ, j, -, hΦc, hj, hΦ⟩ := exists_tensor_adele_equiv (F := F) (E := E)
  have hfin : ∀ x : E, finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x := fun x => by
    rw [show finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from toFinAd_tmul 1 x, map_one, one_mul]
  let u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦc
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  have hdiag : ∀ k : Eˣ, u (Neutral.B1.diagUnits E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := fun k =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ]
      change (algebraMap E (InfiniteAdeleRing E) k, algebraMap E (FiniteAdeleRing (𝓞 E) E) k) = _
      refine Prod.ext (hj k).symm (hfin k).symm))
  have hloc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ),
      u (Neutral.B1.localIdele E W x) = locIdele F W x := fun W x =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ, infTens_locIdele, map_one, finTens_locIdele]
      rfl))
  let H : Formalism.L2.Host.HChar E := ⟨Circle.toUnits.comp (χ.comp u), ht.comp (hχ.1.comp hu), fun k => by
    change Circle.toUnits (χ (u _)) = 1
    rw [hdiag, hχ.2, map_one]⟩
  refine ⟨H, u, fun y => rfl, fun g => ⟨Units.map Φ.toRingHom.toMonoidHom g, Units.ext (Φ.symm_apply_apply _)⟩,
    fun W x => ?_⟩
  change Circle.toUnits (χ (u _)) = Circle.toUnits (χ (locIdele F W x))
  rw [hloc]

theorem eq_one_of_unif_cofinite : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), GlobalTheory.LFun.IsHecke F E χ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ ϖ, Formalism.L2.Host.IsUnifAt w ϖ → χ (GlobalTheory.LFun.locIdele F w ϖ) = 1) → χ = 1 := by
  intro F E _ _ _ _ _ χ hχ hev
  obtain ⟨H, u, hH, hsurj, hloc⟩ := exists_hchar χ hχ
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ ϖ, Formalism.L2.Host.IsUnifAt w ϖ →
      χ (GlobalTheory.LFun.locIdele F w ϖ) = 1}.Finite := Filter.eventually_cofinite.1 hev
  have h1 : H.1 = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away H.1 H.2.1 H.2.2 hfin.toFinset fun v hv x => ?_
    have hv' : ∀ ϖ, Formalism.L2.Host.IsUnifAt v ϖ → χ (GlobalTheory.LFun.locIdele F v ϖ) = 1 := by
      simpa using hv
    refine GlobalTheory.FrobDense.eq_one_of_unif (H.1.comp (Neutral.B1.localIdele E v)) (fun y hy => ?_) x
    change H.loc v y = 1
    rw [hloc, GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.comp_apply, hv' y hy, map_one]
  ext g
  obtain ⟨y, rfl⟩ := hsurj g
  have h2 : Circle.toUnits (χ (u y)) = 1 := (hH y).symm.trans (congrFun (congrArg DFunLike.coe h1) y)
  have h3 : ((χ (u y) : Circle) : ℂ) = 1 := by
    have := congrArg (fun z : ℂˣ => (z : ℂ)) h2
    simpa using this
  simpa using h3

end GlobalTheory.HeckeUnifApprox
end
end

