import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfIsTranslate
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KSRechart

theorem resG_appLE {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U : Y.Opens) {V V' : Z.Opens} (h : V ≤ m ⁻¹ᵁ U) (e : V' ≤ V)
    (r : Γ(Y, U)) : resG Z e ((m.appLE U V h).hom r) = (m.appLE U V' (e.trans h)).hom r := by
  show ((m.appLE U V h) ≫ Z.presheaf.map (homOfLE e).op).hom r = _
  rw [Scheme.Hom.appLE_map]

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart

open scoped Classical in

noncomputable def corr {Z : Scheme.{0}} {n : ℕ} (δ : Fin n → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (W₂ : Z.Opens)
    (θ : Matrix (Fin n) (Fin n) Γ(Z, W₂)) (u : Γ(Z, W₂)ˣ) : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O) :=
  fun O f => if h : O ≤ W₂ then
    ∑ a, ∑ b, resG Z h (θ a b) *
      (δ b O ((Semi.res h u : Γ(Z, O)ˣ) : Γ(Z, O)) * (((Semi.res h u)⁻¹ : Γ(Z, O)ˣ) : Γ(Z, O))) * δ a O f
  else 0

private theorem valR_comp_eq_valR_app' {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (m : Z ⟶ X)
    (U : X.Opens) (O : Z.Opens) (h : O ≤ m ⁻¹ᵁ U) (hO : ⊤ ≤ x ⁻¹ᵁ O) (r : Γ(X, U)) :
    valR x O ((m.appLE U O h).hom r) = valR (x ≫ m) U r := by
  have hU : ⊤ ≤ (x ≫ m) ⁻¹ᵁ U := fun p hp => h (hO hp)
  unfold valR
  rw [dif_pos hO, dif_pos hU]
  congr 1
  show ((m.appLE U O h) ≫ x.appLE O ⊤ hO).hom r = _
  rw [Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart

theorem valR_appLE {X Z : Scheme.{0}} (m : Z ⟶ X) (U : X.affineOpens) {S : Type} [CommRing S] (φ : Γ(X, U.1) →+* S)
    (g₀ : Sp S ⟶ Z) (hg : g₀ ≫ m = spMap φ ≫ chart U) {O : Z.Opens} (h : O ≤ m ⁻¹ᵁ U.1) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (r : Γ(X, U.1)) : valR g₀ O ((m.appLE U.1 O h).hom r) = φ r := by
  rw [valR_comp_eq_valR_app' g₀ m U.1 O h hO r, hg]
  exact GlobalTheory.FlagEmb.QuotLine.valR_chart U.2 φ r

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart

end GlobalTheory.KSRechart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier
open scoped ENNReal

namespace GlobalTheory.CovHt.Link

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

abbrev unf (s : FinalTheorems S κ) : ∀ σ : κ.c.F →+* ℂ, Formalism.L2.Pj.Unf s.Xo κ.c σ N := fun σ => GlobalTheory.ThetaDictCompare.toU (s.U σ)

def wtR (L : CmList A) (u : AllWt.Weight S.Dw) : D.what₂.Tau → Fin N → ℝ :=
  fun t i => u (L.ψ t) (Fin.cast S.rank_eq.symm i)

def drSym (la : AllWt.Weight S.Dw) : Sym D.host.E →₀ ℤ :=
  ∑ z : Letter S.Dw, Finsupp.single (fun _ => false, none, .inl (z.1, z.2)) (-exOf S.Dw la 0 (some z))

theorem expo_drSym (la : AllWt.Weight S.Dw) : expo S.Dw (drSym la) = fun z => -exOf S.Dw la 0 (some z) := by
  classical
  funext x
  have e : ∀ w w' : Sym D.host.E →₀ ℤ, expo S.Dw (w + w') x = expo S.Dw w x + expo S.Dw w' x := fun w w' =>
    Finsupp.sum_add_index' (fun _ => by simp) fun _ _ _ => by split_ifs <;> simp
  let φ : (Sym D.host.E →₀ ℤ) →+ ℤ := AddMonoidHom.mk' (fun w => expo S.Dw w x) e
  change φ _ = _
  rw [drSym, map_sum, Finset.sum_eq_single x (fun z _ hz => ?_) (by simp)]
  · change expo S.Dw _ x = _
    rw [GlobalTheory.Mean4O.expo_single, if_pos (by simp [letterOf])]
  · change expo S.Dw _ x = _
    rw [GlobalTheory.Mean4O.expo_single, if_neg (by simpa [letterOf] using hz)]

variable {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)

theorem divOf_drSym (la : AllWt.Weight S.Dw) : divOf (Φ.C k) (expo S.Dw (drSym la)) = (Φ.C k).Lw la := by
  rw [expo_drSym, GlobalTheory.ShFam.DeKeyTrue.divOf_neg_exOf]

def Over (Z : Comp s.Xo κ.c) : Prop := letI := (constF κ.e (Φ.C k).Y).toAlgebra; LiesOn Z (Φ.C k).y0

def IsCuspSec (la : AllWt.Weight S.Dw) (f : (Φ.C k).Y.Fn) : Prop :=
  f ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) ∧ (Φ.C k).Y.vanishOn ((Φ.C k).Lw la) f (Φ.C k).Ybd

def infSq (x : ToroidalCompactificationData s) (la : AllWt.Weight S.Dw) (σ : D.what₂.LL →+* ℂ) (f : (Φ.C k).Y.Fn) (y : Pts (Φ.C k).Y σ) : ℝ :=
  (cxSt D.what₂.LL).pn (Φ.C k).Y σ ((Φ.C k).Lw la) (GlobalTheory.ShFam.DeKeyTrue.hodgeLw x Φ k σ la)
    ((cxSt D.what₂.LL).cx (Φ.C k).Y σ f) y

def finN (la : AllWt.Weight S.Dw) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (Φ.C k).Y)
    (f : (Φ.C k).Y.Fn) : ℝ :=
  e.w (valAt y.1 (f * (eqn (divOf (Φ.C k) (expo S.Dw (drSym la))) (below y.1) : (Φ.C k).Y.Fn))) *
    Real.exp (lgOf (Φ.C k) (drSym la) v e y)

theorem finN_eq (hm : Mets (Φ.C k) (cxSt D.what₂.LL)) (la : AllWt.Weight S.Dw) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (e : Ext v) (y : AlgPt (Φ.C k).Y) (f : (Φ.C k).Y.Fn) :
    finN Φ k la v e y f = (adlOf (Φ.C k) hm (drSym la)).nrmFin v 1 f e y := by
  simp [finN, Adl.nrmFin, adlOf]

variable (κ) in

def htLog (B : ℝ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ℝ :=
  ∑ p ∈ Pad.setB κ B, -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL)) * htEx D.host.E p

theorem countVol_mono_pos (Dm d : ℕ) {a : ℕ} (ha : 0 < a) {m m' : ℕ → ℕ∞} (h : ∀ τ, 1 ≤ τ → m τ ≤ m' τ) :
    countVol Dm d a m ≤ countVol Dm d a m' :=
  limsup_le_limsup ((eventually_gt_atTop 0).mono fun k hk => ENNReal.div_le_div_right (mul_le_mul_right
    (EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 (h _ (Nat.mul_pos ha hk))))) _) _)

theorem le_volSlope_of_le {δ W a : ℝ} (hδ : δ ≤ W) (hW : 0 < W) {vol : ℝ → ℝ≥0∞}
    (h : ∀ t, ENNReal.ofReal (W * (a + t)) ≤ vol t) : (a : EReal) ≤ volSlope δ vol := by
  refine ((le_volSlope_iff hW vol a).2 h).trans (iInf_mono fun t => EReal.sub_le_sub ?_ le_rfl)
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal hδ) _)

theorem le_volSlope_of_tendsto {δ W sl c C : ℝ} {Dm : ℕ} {ar dg : ℚ → ℝ} {vol : ℝ → ℝ≥0∞} (hδ : δ ≤ W) (hW : 0 < W)
    (hd : Tendsto dg (𝓝[>] 0) (𝓝 W)) (ha : Tendsto (fun r => ar r / (((Dm : ℝ) + 1) * dg r)) (𝓝[>] 0) (𝓝 sl))
    (h : ∀ᶠ r : ℚ in 𝓝[>] 0, ∀ t, ENNReal.ofReal (ar r / ((Dm : ℝ) + 1) + dg r * (t - c - C * r)) ≤ vol t) :
    ((sl - c : ℝ) : EReal) ≤ volSlope δ vol := by
  refine le_volSlope_of_le hδ hW fun t => ?_
  have hr : Tendsto (fun r : ℚ => (r : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Rat.continuous_coe_real.tendsto 0).mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun r : ℚ => dg r * (ar r / (((Dm : ℝ) + 1) * dg r)) + dg r * (t - c - C * r)) (𝓝[>] 0)
      (𝓝 (W * sl + W * (t - c - C * 0))) :=
    (hd.mul ha).add (hd.mul (tendsto_const_nhds.sub (hr.const_mul C)))
  have e : W * sl + W * (t - c - C * 0) = W * (sl - c + t) := by ring
  rw [e] at h1
  refine le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp h1) ?_
  filter_upwards [h, hd.eventually (lt_mem_nhds hW)] with r h2 h3
  refine le_of_eq_of_le (congrArg ENNReal.ofReal ?_) (h2 t)
  have := h3.ne'
  field_simp

end GlobalTheory.CovHt.Link

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureDescendsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_descends : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S₀ : Scheme.{0}}
    {X : Obj F 𝔠 S} {X₀ : Obj F 𝔠 S₀} {b : S₀ ⟶ S} {i : X₀.A.left ⟶ X.A.left}, X₀.IsPullBy X b i →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), ∃ t₀ : Sp Ω ⟶ S₀, t₀ ≫ b = t) →
    ∀ {N : ℕ} (α₀ : X₀.Level N) (q : Fin 2 → (𝟙_ (Over S) ⟶ X.A)), (∀ k, q k ^ N = 1) →
    (∀ k, (α₀.pt k).left ≫ i = b ≫ (q k).left) → Nonempty (X.Level N) := by
  first | exact @GlobalTheory.RealMult.level_descend | exact GlobalTheory.RealMult.level_descend | (intros; apply GlobalTheory.RealMult.level_descend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelUnitThetaConstantNeZeroDividesAllStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_unit_thetaConstant_ne_zero_divides_all : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) ∧ 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 ∧ ∀ a, ∃ r : V, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
  first | exact @GlobalTheory.Poinc.IntTerm.unit_ne_zero_dvd | exact GlobalTheory.Poinc.IntTerm.unit_ne_zero_dvd | (intros; apply GlobalTheory.Poinc.IntTerm.unit_ne_zero_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCorrespondenceDifferentialsStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_correspondence_differentials : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E) (𝔠 : FracId (FR E))
    (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left) (U : Unif φ L 0 X)
    (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
    X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom) →
    ∃ (δ₀ : X₀.DetGen) (δ : X.DetGen) (C : ℂ), Obj.DetCorr (algebraMap Qb ℂ) p δ₀.1 δ.1 ∧ U.IsDet δ.1 C ∧
      IsAlgebraic ℚ (C * ∏ i, a i) := by
  first | exact @GlobalTheory.LatJet.exists_detGen_coeff_algebraic | exact GlobalTheory.LatJet.exists_detGen_coeff_algebraic | (intros; apply GlobalTheory.LatJet.exists_detGen_coeff_algebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiePairingCanonicalRigidifiedExtensionTangent
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem lie_psi_cl_eq_tanVal : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (ψ : PrimitiveSubmodule A →ₗ[R] G.omega), (∀ c : PrimitiveSubmodule A, IsCan t c.1 (G.rigOfOmega (ψ c))) → ∀ (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A) (hF : (⟨_, hβ⟩ : primDR A) ∈ PrimitiveSubmodule A) (x : G.Lie) (v : epsR R ⟶ A), t.LieCorr x v → x (ψ ⟨_, hF⟩) = tanVal v β := by
  intro p _ R _ N hN A _ hA G t ψ hψ β hβ hF x v hx
  obtain ⟨w, hw1, hw2⟩ := isCan_form R A p G t β hβ
  have hw : ψ ⟨_, hF⟩ = w :=
    PDivGroup.rigOfOmega_injective_of_pow p R N hN G (isCan_unique R A p G t _ hA _ _ (hψ _) hw2)
  rw [hw]
  exact lie_cotVal_eq_tanVal R A p G t ⟨N, hN⟩ β w hw1 x v hx

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangePadicIntInjectiveSaturatedOfModL
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatticeModL

theorem exists_one_tmul_add_smul (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H]
    (x : ℤ_[l] ⊗[ℤ] H) :
    ∃ (h : H) (y : ℤ_[l] ⊗[ℤ] H), x = (1 : ℤ_[l]) ⊗ₜ h + (l : ℤ_[l]) • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a h =>
    obtain ⟨c, hc⟩ : ∃ c : ℤ_[l], a - (a.zmodRepr : ℤ_[l]) = (l : ℤ_[l]) * c := by
      have := PadicInt.sub_zmodRepr_mem a
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
      exact this
    refine ⟨(a.zmodRepr : ℤ) • h, c ⊗ₜ h, ?_⟩
    have ha : a = ((a.zmodRepr : ℤ) : ℤ_[l]) + (l : ℤ_[l]) * c := by
      rw [← hc]; push_cast; ring
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, zsmul_eq_mul, _root_.mul_one, ← TensorProduct.add_tmul, ← ha]
  | add x y hx hy =>
    obtain ⟨h₁, y₁, rfl⟩ := hx
    obtain ⟨h₂, y₂, rfl⟩ := hy
    exact ⟨h₁ + h₂, y₁ + y₂, by rw [TensorProduct.tmul_add, smul_add]; abel⟩

end GlobalTheory.LatticeModL

open GlobalTheory.LatticeModL in

theorem GlobalTheory.latticeMap_liftBaseChange_injective_saturated :
    ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [Module.Finite ℤ H] [Module.Free ℤ H]
      [AddCommGroup T] [Module ℤ_[l] T], (∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0) →
      ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') →
      Function.Injective (φ.toIntLinearMap.liftBaseChange ℤ_[l]) ∧
      ∀ t : T, (l : ℤ_[l]) • t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) →
        t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) := by
  intro l _ H T _ _ _ _ _ htor φ hsat
  set F := φ.toIntLinearMap.liftBaseChange ℤ_[l] with hFdef
  have hF : ∀ h, F ((1 : ℤ_[l]) ⊗ₜ h) = φ h := by
    intro h; simp [F]
  have key : ∀ (x : ℤ_[l] ⊗[ℤ] H) (t : T), F x = (l : ℤ_[l]) • t →
      ∃ x', x = (l : ℤ_[l]) • x' := by
    intro x t hx
    obtain ⟨h, y, rfl⟩ := exists_one_tmul_add_smul l H x
    rw [map_add, map_smul, hF] at hx
    have h1 : φ h = (l : ℤ_[l]) • (t - F y) := by rw [smul_sub, ← hx]; abel
    obtain ⟨h', rfl⟩ := hsat h _ h1
    refine ⟨(1 : ℤ_[l]) ⊗ₜ h' + y, ?_⟩
    rw [smul_add, TensorProduct.tmul_smul]
    simp only [Nat.cast_smul_eq_nsmul]
  have hl : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal ℤ_[l]) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨x', rfl⟩ := key x 0 (by rw [hx, smul_zero])
    have : F x' = 0 := htor _ (by rw [← map_smul, hx])
    exact Submodule.smul_mem_smul hl this
  · rintro t ⟨x, hx⟩
    obtain ⟨x', rfl⟩ := key x t hx
    refine ⟨x', ?_⟩
    have : (l : ℤ_[l]) • (F x' - t) = 0 := by rw [smul_sub, ← map_smul, hx, sub_self]
    exact sub_eq_zero.mp (htor _ this)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTorsionPointNilpotentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_torsion_point_nilpotent : ∀ {R : Type} [CommRing R] [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ), (∀ x ∈ RingHom.ker π, IsNilpotent x) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (G₀ : Over (Sp ℂ)) [GrpObj G₀] (i : G₀.left ⟶ G.left), IsGrpPullback G₀ G (spMap (π : R →+* ℂ)) i →
    ∀ (N : ℕ), 1 ≤ N → ∀ (p : 𝟙_ (Over (Sp ℂ)) ⟶ G₀), p ^ N = 1 →
    ∃ q : 𝟙_ (Over (Sp R)) ⟶ G, q ^ N = 1 ∧ p.left ≫ i = spMap (π : R →+* ℂ) ≫ q.left := by
  first | exact @GlobalTheory.TorsionLift.exists_torsion_lift | exact GlobalTheory.TorsionLift.exists_torsion_lift | (intros; apply GlobalTheory.TorsionLift.exists_torsion_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleEndoFactorPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM

open GlobalTheory.CechPic GlobalTheory.RealMult.Elliptic

theorem hasGen_lam_pull_of_lbIso {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {M M' : LB A.left}
    (hM : M.IsLB) (hM' : M'.IsLB) (α : A ⟶ A)
    (h : LBIso (abelian₂ A M') ((abelian₂ A M).pull (lift (fst A A) (snd A A ≫ α)).left)) {T : Over S} (x : T ⟶ A)
    (hx : HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left)) :
    HasGen ((abelian₂ A M').pull (lift (fst A T) (snd A T ≫ x)).left) := by
  have hl : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hl' : (abelian₂ A M').IsLB := LB.isLB_linComb hM' _ _
  have h₁ : lam (cls M' hM') (fst A A) (snd A A) = lam (cls M hM) (fst A A) (snd A A ≫ α) :=
    (cls_cube_two hM' _ _ hl').symm.trans
      (((cls_eq_iff hl' (pull_isLB hl _)).2 h).trans (cls_pull_lam hM _ _ _))
  have h₂ : lam (cls M hM) (fst A T) (snd A T ≫ x) = 0 :=
    (cls_pull_lam hM _ _ (pull_isLB hl _)).symm.trans ((cls_eq_zero_iff (pull_isLB hl _)).2 hx)
  have h₃ := congrArg (CechPic.pull (lift (snd A T ≫ x) (fst A T)).left) h₁
  have h₄ := congrArg (CechPic.pull (lift (fst A T ≫ α) (snd A T)).left) h₂
  rw [pull_lam, pull_lam, lift_fst, lift_snd, lift_snd_assoc] at h₃
  rw [pull_lam, map_zero, lift_fst, lift_snd_assoc] at h₄
  refine (cls_eq_zero_iff (pull_isLB hl' _)).1 ?_
  rw [cls_pull_lam hM', lam_comm, h₃, lam_comm, h₄]

theorem comp_eq_one_of_lam_triv_of_pull_pos : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (f : A ⟶ A),
    M.IsLB → IsFactorAH u Hm χ →
    ∀ (M' : LB A.left) (u' : HolUnif A M' g) (Hm' : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ) (α : A ⟶ A),
    M'.IsLB → u'.IsAH Hm' χ' → IsMonHom α → LBIso (abelian₂ A M') ((abelian₂ A M).pull (lift (fst A A) (snd A A ≫ α)).left) →
    (∀ w, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → u.ex w ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ≫ f = 1 := by
  intro g A _ hA M u Hm χ f hM hF M' u' Hm' χ' α hM' hAH _ hiso hf T x hx
  haveI := hA.comm
  obtain ⟨P, ψ, ρ, N, hN, hψ, hρ, h₁, h₂, h₃⟩ := GlobalTheory.T.polarized_abelian_isogeny_exists g A hA M' u' Hm' χ' hM' hAH
  have hk : x ^ (N * N) = 1 := GlobalTheory.T.isogeny_torsion_generator_power A hA M' hM' P ψ ρ N hψ hρ h₁ h₂ h₃ T x
    (hasGen_lam_pull_of_lbIso hM hM' α hiso x hx)
  refine GlobalTheory.T.torsion_generator_char_trivial A hA M f (N * N) hM (Nat.mul_pos hN hN) (fun y hy => ?_) T x hk hx
  obtain ⟨w, rfl⟩ := u.ex_onto y
  obtain ⟨θ, hθ, h0, hp⟩ := GlobalTheory.T.theta_multiplier_trivialization g A hA M u Hm χ hM hF w hy
  exact hf w (GlobalTheory.T.theta_multiplier_integral_imaginary g u.Λ u.full Hm hF.1 w θ hθ h0 hp)

end GlobalTheory.TorusRM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGenericFibreExtendsOverDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem lb_extends_over_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (H : Over (Sp R)) [Smooth H.hom] [QuasiCompact H.hom] [IsSeparated H.hom] [GeometricallyIntegral H.hom] (L : LB ((Over.pullback (jK R)).obj H).left), L.IsLB → ∃ L' : LB H.left, L'.IsLB ∧ LBIso L (L'.pull (pullback.fst H.hom (jK R))) := by
  intro R _ _ _ H _ _ _ _ L hL
  obtain ⟨M, hM, hML⟩ := GlobalTheory.LBExtDVR.exists_lineBundle_extension_genericFibre R (FractionRing R)
    H.left ((Over.pullback (jK R)).obj H).left H.hom (pullback.snd H.hom (jK R))
    (pullback.fst H.hom (jK R)) inferInstance inferInstance (IsPullback.of_hasPullback H.hom (jK R)) L hL
  exact ⟨M, hM, LBIso.symm hML⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordOfGenericExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_mumford_of_generic_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L' : LB G.left) (N : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L'.IsLB → N.IsLB → LBIso N (L'.pull (pullback.fst G.hom (jK R))) → ExtLam G N PP → LBIso (abelian₂ G L') PP := by
  first | exact @GlobalTheory.Mum.lbIso_lam_of_extLam | exact GlobalTheory.Mum.lbIso_lam_of_extLam | (intros; apply GlobalTheory.Mum.lbIso_lam_of_extLam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionEqOfIsoStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_eq_of_iso : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (C : Type) [Category.{0} C] (G : C ⥤ AffOp X₀) (d d' : GlobalTheory.CatCoh.H2 (ext R₁ (G ⋙ OAff s₀))), L.IsLB → L'.IsLB → LBIso L L' → ObAt S α L G d → ObAt S α L' G d' → d = d' := by
  first | exact @GlobalTheory.LBObsUniq.obAt_eq_of_iso | exact GlobalTheory.LBObsUniq.obAt_eq_of_iso | (intros; apply GlobalTheory.LBObsUniq.obAt_eq_of_iso <;> assumption)
end

