import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3033
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3226
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.NefEffectiveCones.EventuallyEvalNegOfCoeffNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2957
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3371

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceClosedFibreModificationFieldExtens
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) := by
  intro R _ _ _ hA M K _ κ
  obtain ⟨hN, -, hIC, -⟩ := hA
  haveI := hN
  haveI := hIC
  obtain ⟨hbij, hsurj⟩ := Modif.appTop_bijective_surjective R M
  haveI := M.proper
  haveI := hsurj
  have hcomp : ∀ {A : Type} [CommRing A] (ψ : ResidueField R →+* A),
      spMap ψ ≫ spMap (residue R) = spMap (ψ.comp (residue R)) := fun ψ => by
    rw [← Spec.map_comp]; rfl
  have pc : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) [PreconnectedSpace X], PreconnectedSpace Y :=
    fun h _ => ⟨by rw [← h.surjective.range_eq, ← Set.image_univ]; exact isPreconnected_univ.image _ h.continuous.continuousOn⟩
  let f := pullback.snd M.π (spMap (residue R))
  have e : ∀ {A : Type} [CommRing A] (ψ : ResidueField R →+* A),
      pullback f (spMap ψ) ≅ pullback M.π (spMap (ψ.comp (residue R))) := fun ψ =>
    pullbackLeftPullbackSndIso M.π (spMap (residue R)) (spMap ψ) ≪≫ pullback.congrHom rfl (hcomp ψ)
  have hP : PreconnectedSpace (pullback f (spMap κ) : Scheme.{0}) := by
    refine GlobalTheory.T.preconnectedSpace_of_finGen_subfield_baseChanges (ResidueField R) _ f inferInstance inferInstance K κ fun L hL n c hc => ?_
    have hc' := GlobalTheory.T.connectedSpace_closedFibre_finitelyGenerated_ext R M.S M.π inferInstance hsurj hbij K κ L hL n c hc
    exact @pc _ _ _ _ (Scheme.homeoOfIso (e _)).symm hc'.toPreconnectedSpace
  haveI : PreconnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) :=
    pc (Scheme.homeoOfIso (e κ))
  obtain ⟨q⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨z, -⟩ := (pullback.snd M.π (spMap (κ.comp (residue R)))).surjective q
  exact ConnectedSpace.mk ⟨z⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelianStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_to_h1_structure_surjective_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) := by
  first | exact @GlobalTheory.PtExt.toH1O_surjective_of_abelian | exact GlobalTheory.PtExt.toH1O_surjective_of_abelian | (intros; apply GlobalTheory.PtExt.toH1O_surjective_of_abelian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseAffineChartPreimageInterior
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalProj

theorem chart_dense_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens), Dense ((chart U).base ⁻¹' (interior Y : Set Y.X)) := by
  intro E _ _ _ H Dw l Xo c Y U
  have hi := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have h : IsOpenMap (chart U).base := (Scheme.Hom.isOpenEmbedding (f := U.2.fromSpec)).isOpenMap
  exact (dense_interior Y).preimage h

end GlobalTheory.BalProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendStalkOfIsoStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_stalk_extend_of_app : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f] (U : X.affineOpens) (d : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1), ∃ δ : Derivation ℤ (X'.presheaf.stalk x) (X'.presheaf.stalk x), ∀ r, δ ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom r)) = (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom (d r)) := by
  first | exact @GlobalTheory.StalkDer.derivation_extend_stalk_of_iso | exact GlobalTheory.StalkDer.derivation_extend_stalk_of_iso | (intros; apply GlobalTheory.StalkDer.derivation_extend_stalk_of_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneHodgeFiltrationPerfectFieldStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonne_hodgeFiltration_perfectField : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), (∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧ (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧ (∀ m, G.rigToLie (p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧ Function.Injective G.rigOfOmega := by
  first | exact @GlobalTheory.Dieu.Theory.hodge_filtration | exact GlobalTheory.Dieu.Theory.hodge_filtration | (intros; apply GlobalTheory.Dieu.Theory.hodge_filtration <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelPersistsThetaSetupTower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem Tower.div_lam : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hx V _ _ _ ev X _ m t δ _
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hdvd : X₁.S.r * X₁.S.N ∣ 𝔗.X₂.S.r * 𝔗.X₂.S.N := ⟨𝔗.d, 𝔗.lev⟩
  obtain ⟨a, ha, hdv⟩ := DivDeep.exists_div_torsion 𝔗.X₂ 𝔗.isAct z₂
    (X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)) hdvd
  have hL : 0 < 𝔗.X₂.S.r * 𝔗.X₂.S.N := Nat.mul_pos 𝔗.X₂.S.r_pos (by have := 𝔗.X₂.S.N_ge; omega)
  choose x hxa using fun s => DivDeep.exists_eq_smul_of_smul_eq_zero hL hdvd (a s) (congrFun ha s)
  have hd : 𝔗.X₂.S.r * 𝔗.X₂.S.N / (X₁.S.r * X₁.S.N) = 𝔗.d := by
    rw [𝔗.lev]; exact Nat.mul_div_cancel_left _ hk
  rw [hd] at hxa
  obtain ⟨b, hb⟩ := 𝔗.lam_range x
  obtain rfl : 𝔗.lam b = a := hb.trans (funext hxa)
  obtain ⟨k, hk, e⟩ := DivDeep.same_ratio (GlobalTheory.T.thetaSetupTower_same_genericFibre_realisations g n F W Z i X₁ act hact 𝔗) x₀ b
  set φ := algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁
  have h₁ : φ (X₁.S.th x₀) ≠ 0 := (map_ne_zero φ).2 hx.1
  have h₂ := hdv.1
  have h₃ : 𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b) ≠ 0 := fun h => by
    rw [h, zero_pow hk.ne'] at e
    exact pow_ne_zero k (mul_ne_zero h₂ h₁) e.symm
  have h₄ := left_ne_zero_of_mul h₃
  have h₅ := right_ne_zero_of_mul h₃
  have hN : IsIntegrallyClosed (𝔗.X₂.M.O z₂) := RatModel.isIntegrallyClosed_O (fun z => by
    haveI := 𝔗.X₂.normal
    exact ⟨𝔗.X₂.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩) z₂
  have m₁ : 𝔗.X₂.S.th (𝔗.lam b) * φ (X₁.S.th x₀) / (𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b)) ∈ 𝔗.X₂.M.O z₂ :=
    DivDeep.root_mem_O hN hk (by rw [div_pow, e, div_self (pow_ne_zero k (mul_ne_zero h₂ h₁))])
  have m₂ : φ (X₁.S.th b / X₁.S.th x₀) ∈ 𝔗.X₂.M.O z₂ := by
    obtain ⟨U, f, hU, hf⟩ := hx.2 b
    refine ⟨𝔗.p ⁻¹ᵁ U, 𝔗.p.app U f, show 𝔗.p z₂ ∈ U from hz₂ ▸ hU, ?_⟩
    refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
    rw [𝔗.p_pt, ← hf]
    exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hU⟩) f
  refine ⟨h₄, fun j => ?_⟩
  have := mul_mem (hdv.2 j) (mul_mem m₁ m₂)
  convert this using 1
  rw [map_div₀]
  field_simp

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitEqOfGermEqStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumber_unit_eq_of_germ_eq : ∀ (k : Type) [Field k] (z : Sp (DualNumber k)) (u v : (DualNumber k)ˣ), gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn u) = gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn v) → u = v := by
  first | exact @GlobalTheory.DualUnitGerm.unit_eq_of_germ_eq | exact GlobalTheory.DualUnitGerm.unit_eq_of_germ_eq | (intros; apply GlobalTheory.DualUnitGerm.unit_eq_of_germ_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveDivisorPosDegreeAmpleClass
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.EffPos

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Cartier

theorem exists_coheight_eq_one_notMem {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {M : LB X}
    (hM : M.IsLB) (s : M.Sec) (hs : genericPoint X ∈ nonzeroLocus s) {x : X} (hx : x ∉ nonzeroLocus s) :
    ∃ w : X, Order.coheight w = 1 ∧ w ∉ nonzeroLocus s := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ M.U i := by
    have : x ∈ (⨆ i, M.U i : X.Opens) := by rw [hM.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  set g := X.presheaf.germ _ x hi (s.f i) with hgdef
  have hg0 : g ≠ 0 := GlobalTheory.MixHt.CycLoc.germ_ne_zero hs hi
  have hgu : ¬ IsUnit g := fun h =>
    hx ((Cartier.mem_nonzeroLocus_iff s i hi).2 ((Scheme.mem_basicOpen _ _ _ _).2 h))
  have hle : Ideal.span {g} ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal _).2 hgu)
  obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le hle
  have hPp : P.IsPrime := hP.1.1
  have h1 : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
  have hgP : g ∈ P := hP.1.2 (Ideal.subset_span rfl)
  have hP0 : (⊥ : Ideal (X.presheaf.stalk x)) < P := bot_lt_iff_ne_bot.2 fun h =>
    hg0 (by rw [h] at hgP; simpa using hgP)
  have e0 := Ideal.height_add_one_le_of_lt_of_isPrime hP0
  rw [Ideal.height_bot, zero_add] at e0
  refine ⟨X.fromSpecStalk x ⟨P, hPp⟩, ?_, ?_⟩
  · rw [GlobalTheory.MixHt.CycLoc.coheight_fromSpecStalk]
    exact le_antisymm h1 e0
  · rw [GlobalTheory.MixHt.CycLoc.mem_nonzeroLocus_iff_notMem s hi, not_not]
    exact hgP

end GlobalTheory.AV.EffPos

namespace GlobalTheory.AV.EffPos

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Cartier

theorem interNumRed_pos {K : Type} [Field K] (A : AbVar K) (n : ℕ) (hdim : A.dim = n + 1)
    (L : LB A.X.left) (hL : L.IsLB) (hLa : IsAmpleLB L) {w : A.X.left} (hw : Order.coheight w = 1) :
    letI := A.algΓ
    0 < interNumRed K (⟨closure {w}, isClosed_closure⟩ : Closeds A.X.left) (fun _ : Fin n => L) := by
  letI := A.algΓ
  obtain ⟨hint, hnoeth, -⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  obtain ⟨hstr, hproj⟩ := AbVarProj.strHom_eq_and_isProjOver K A
  have hp : IsProjOver (strHom K A.X.left) := hstr ▸ hproj
  have hX : topologicalKrullDim A.X.left = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_dim, hdim]
  have : LocallyOfFiniteType (strHom K A.X.left) := by
    obtain ⟨N, j, _, h⟩ := hp
    exact h ▸ inferInstance
  set C : Closeds A.X.left := ⟨closure {w}, isClosed_closure⟩ with hC
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  letI := algebraΓAlong K (redι C)
  rw [interNumRed_def, interNumSub_def,
    interNumOn_eq_interNum_pull (k := K) (f := redι C) (fun _ => rfl) (fun _ => hL)]
  have hd : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal C).subscheme = (n : WithBot ℕ∞) := by
    rw [topologicalKrullDim_red]
    exact VdmRec.CutSec.dim_closure_of_coheight_field (strHom K A.X.left) hX hw
  exact CompanionTheory.NefKleiman.interNum_top_pos_of_isAmpleLB K _ (PullVanish.isProjOver_red hp C) n hd _
    (hLa.pull_of_isClosedImmersion (redι C))

theorem inter_cons_pos : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left), IsAmpleCls c → ∀ (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), Out.nonzeroLocus s ≠ ⊥ → Out.nonzeroLocus s ≠ ⊤ → 0 < inter A (Fin.cons (cls M hM) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  intro K _ A n hdim c hc M hM s hbot htop
  obtain ⟨L, hL, hrel, rfl⟩ := hc
  have hLa : IsAmpleLB L := (AmpleClsIff.isAmpleCls_cls_iff K A L hL).1 ⟨L, hL, hrel, rfl⟩
  letI := A.algΓ
  obtain ⟨hint, hnoeth, hcpt⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  obtain ⟨hstr, hproj⟩ := AbVarProj.strHom_eq_and_isProjOver K A
  have hp : IsProjOver (strHom K A.X.left) := hstr ▸ hproj
  have hX : topologicalKrullDim A.X.left = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_dim, hdim]
  have hcons : ∀ j, ((Fin.cons M (fun _ : Fin n => L) : Fin (n + 1) → LB A.X.left) j).IsLB :=
    fun j => Fin.cases hM (fun _ => hL) j
  have hfam : (Fin.cons (cls M hM) (fun _ : Fin n => cls L hL) : Fin (n + 1) → Pic A.X.left) =
      fun j => cls ((Fin.cons M (fun _ : Fin n => L) : Fin (n + 1) → LB A.X.left) j) (hcons j) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp
  rw [hfam, T.abelianVariety_intersection_eq_lineBundleIntersection K A (Fin (n + 1)) _ hcons]
  have hs : genericPoint A.X.left ∈ nonzeroLocus s := by
    obtain ⟨y, hy⟩ : (nonzeroLocus s : Set A.X.left).Nonempty := by
      by_contra h
      exact hbot (TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.1 h))
    exact ((genericPoint_spec A.X.left).mem_open_set_iff (nonzeroLocus s).isOpen).2 ⟨y, trivial, hy⟩
  rw [SecCycle.interNum_cons_eq_finsum_mult K A.X.left hp n hX.le M hM (fun _ => L) (fun _ => hL) s hs]
  obtain ⟨x, hx⟩ : ∃ x, x ∉ nonzeroLocus s := by
    by_contra h
    push_neg at h
    exact htop (eq_top_iff.2 fun x _ => h x)
  obtain ⟨w, hw1, hws⟩ := exists_coheight_eq_one_notMem hM s hs hx
  have hfs := (divOfSec hM s hs).finite_support_mult
  have hterm : ∀ v, 0 ≤ (divOfSec hM s hs).mult v *
      interNumRed K (⟨closure {v}, isClosed_closure⟩ : Closeds A.X.left) (fun _ : Fin n => L) := by
    intro v
    by_cases hv : (divOfSec hM s hs).mult v = 0
    · rw [hv, zero_mul]
    · exact mul_nonneg (mult_divOfSec_nonneg v)
        (interNumRed_pos A n hdim L hL hLa (CartierDiv.coheight_eq_one_of_mult_ne_zero hv)).le
  have hmw : (divOfSec hM s hs).mult w ≠ 0 := SecCycle.mult_divOfSec_ne_zero hM s hs hw1 hws
  have hw0 : 0 < (divOfSec hM s hs).mult w *
      interNumRed K (⟨closure {w}, isClosed_closure⟩ : Closeds A.X.left) (fun _ : Fin n => L) :=
    mul_pos (lt_of_le_of_ne (mult_divOfSec_nonneg w) (Ne.symm hmw)) (interNumRed_pos A n hdim L hL hLa hw1)
  rw [finsum_eq_sum_of_support_subset _ (s := hfs.toFinset) ?_]
  · exact Finset.sum_pos' (fun v _ => hterm v) ⟨w, by simpa using hmw, hw0⟩
  · intro v hv
    simpa using Function.support_mul_subset_left _ _ hv

end GlobalTheory.AV.EffPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenRankInteriorEqSignature
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BalProjInt

open GlobalTheory.ShFam.Pad GlobalTheory.ArLieBase GlobalTheory.BalProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tan_act {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x0 : Sp S ⟶ X} (a : 𝓞 E)
    {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : IsTanAtG t x0 (v ≫ (t.act.act a).left) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, Over.w]; exact hv.1
  · rw [← Category.assoc, hv.2, ← Over.comp_left]
    congr 1
    haveI := t.act.hom a
    rw [Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem comb_act_mat {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x0 : Sp S ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hu : ∀ i, IsTanAtG t x0 (u i)) (a : 𝓞 E)
    {B : Matrix (Fin m) (Fin m) S} (hB : ∀ i, IsCombAtG t x0 u (B i) (u i ≫ (t.act.act a).left))
    {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsCombAtG t x0 u cf w) :
    IsCombAtG t x0 u (cf ᵥ* B) (w ≫ (t.act.act a).left) := by
  have := t.act.hom a
  have hu' := fun i => tan_act t a (hu i)
  have h2 : IsCombAtG t x0 (fun i => u i ≫ (t.act.act a).left) cf (w ≫ (t.act.act a).left) := by
    have h1 := (isCombAtG_iff t x0 (fun j => ovT (hu j)) cf w).1 hw
    refine (isCombAtG_iff t x0 (fun j => ovT (hu' j)) cf _).2 ?_
    rw [← h1, ← Over.comp_left, combT_post]
    congr 2
  have h3 := tanLinG u hu _ Bᵀ cf _ (fun i => hB i) h2
  rwa [Matrix.mulVec_transpose] at h3

theorem affineOpenChart_comp_structure_eq_spMap {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of K)) (U : X.affineOpens) :
    chart U ≫ s = spMap (fnHom s U.1) := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Spec (CommRingCat.of K))) U.2
    (le_top : U.1 ≤ s ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  rw [chart, ← e, ← Spec.map_comp]
  rfl

theorem exists_eig_subspace_gen {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Z : Model Xo c β) {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)) (he : GlobalTheory.LineNorm.IsTanBasis Z.t x e) (K : Type) [Field K]
    (ψ : R →+* K) (φ : c.F →+* K) (hφ : spMap ψ ≫ x ≫ Z.s = spMap (φ.comp β)) :
    ∃ V : Submodule K (Fin g → K), Module.finrank K V = Dw.mult τ ∧
      ∀ (cf : Fin g → K) (w : Sp (DualNumber K) ⟶ Z.t.G.left),
        IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w →
          (IsEigTan Z φ (spMap ψ ≫ x) τ w ↔ cf ∈ V) := by
  have h0 : (spMap ψ ≫ x) ≫ Z.s = spMap φ ≫ spMap β := by
    rw [Category.assoc, hφ, Guard.sp_comp]
  let y : Sp K ⟶ gen Z := Limits.pullback.lift (spMap ψ ≫ x) (spMap φ) h0
  have hy1 : y ≫ genι Z = spMap ψ ≫ x := Limits.pullback.lift_fst _ _ _
  have hy2 : y ≫ genStr Z = spMap φ := Limits.pullback.lift_snd _ _ _
  have hf := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c _ _ Z K φ y hy2
  rw [hy1] at hf
  obtain ⟨f⟩ := hf
  have hv : ∀ i, IsTanAtG Z.t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ e i) :=
    fun i => GlobalTheory.FactorDepth.isTanAtG_map Z.t ψ (he.1 i)
  have hb := he.2 K ψ
  choose a ha using fun i => (hb _ (f.tan τ i)).exists
  let A : Matrix (Fin g) (Fin (Dw.mult τ)) K := fun j i => a i j
  have heig : ∀ cf w, IsCombAtG Z.t (spMap ψ ≫ x) (f.v τ) cf w → ∀ b : 𝓞 E,
      w ≫ (Z.t.act.act b).left = spMap (epsMul (φ (embK c τ b))) ≫ w := fun cf w h1 b => by
    rw [← (isCombAtG_iff Z.t _ (fun j => ovT (f.tan τ j)) _ _).1 h1]
    have := Z.t.act.hom b
    exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (f.tan τ j)) (Z.t.act.act b) _
      (fun j => Over.OverMorphism.ext (f.eig τ j b)) cf)
  have hi : Guard.Indep Z.t (spMap ψ ≫ x) (f.v τ) := fun cf cf' w h1 h2 =>
    (f.basis τ w (Guard.comb_tan (f.tan τ) h1) (heig cf w h1)).unique h1 h2
  have hinj := (Guard.indep_iff hv (Guard.indep_of_basis hv hb) A ha).1 hi
  refine ⟨LinearMap.range A.mulVecLin, ?_, fun cf w hw => ⟨fun h => ?_, ?_⟩⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  · obtain ⟨b, hb', -⟩ := f.basis τ w h.1 h.2
    exact ⟨b, (hb w h.1).unique (tanLinG _ hv (f.v τ) A b w ha hb') hw⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨w', h1, h2⟩ := Guard.exists_comb (f.tan τ) b
    obtain rfl : w' = w := Guard.comb_unique hv (tanLinG _ hv (f.v τ) A b w' ha h2) hw
    exact ⟨h1, heig b w' h2⟩

theorem mem_eigSp {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k) (c : Fin n → k) :
    c ∈ eigSp B χ ↔ ∀ a, c ᵥ* B a = χ a • c := Iff.rfl

theorem eigRank_field {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left))
    (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (hv : ∀ i, IsTanAtG Y.t (chart U) (v i))
    (hb : ∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w)
    (hA : ∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) (K : Type) [Field K]
    (ψ : Γ(Y.X, U.1) →+* K) (τ : E →+* ℂ) :
    eigRank ψ A (embR c.F c.conj (fnHom Y.s U.1) τ) = Dw.mult τ := by
  let φ : c.F →+* K := ψ.comp (fnHom Y.s U.1)
  have he := GlobalTheory.LineNorm.isTanBasis_of_basis E H Y.X Y.t Γ(Y.X, U.1) (chart U) n v hv hb
  have hφ : spMap ψ ≫ chart U ≫ Y.s = spMap (φ.comp (RingHom.id c.F)) := by
    rw [affineOpenChart_comp_structure_eq_spMap, Guard.sp_comp]
  obtain ⟨V, hVr, hV⟩ := exists_eig_subspace_gen Y (chart U) τ v he K ψ φ hφ
  have hvK : ∀ i, IsTanAtG Y.t (spMap ψ ≫ chart U) (spMap (dualMap ψ) ≫ v i) :=
    fun i => GlobalTheory.FactorDepth.isTanAtG_map Y.t ψ (hv i)
  have hbK := he.2 K ψ
  have hAK : ∀ a i, IsCombAtG Y.t (spMap ψ ≫ chart U) (fun j => spMap (dualMap ψ) ≫ v j) ((A a).map ψ i)
      ((spMap (dualMap ψ) ≫ v i) ≫ (Y.t.act.act a).left) := fun a i => by
    rw [Category.assoc]
    exact GlobalTheory.LatDRFree.comb_map Y.t ψ (hA a i)
  have key : eigSp (fun a => (A a).map ψ) (fun a => ψ (embR c.F c.conj (fnHom Y.s U.1) τ a)) = V := by
    ext cf
    obtain ⟨w, -, hw⟩ := Guard.exists_comb hvK cf
    rw [← hV cf w hw]
    have hs : ∀ a : 𝓞 E, ψ (embR c.F c.conj (fnHom Y.s U.1) τ a) • cf = fun k => φ (embK c τ a) * cf k :=
      fun a => rfl
    rw [mem_eigSp]
    constructor
    · intro h
      refine ⟨Guard.comb_tan hvK hw, fun a => ?_⟩
      have h1 := comb_act_mat Y.t hvK a (hAK a) hw
      rw [h a, hs a] at h1
      exact Guard.comb_unique hvK h1 (Guard.comb_smul hvK hw (φ (embK c τ a)))
    · rintro ⟨-, h⟩ a
      have h1 := comb_act_mat Y.t hvK a (hAK a) hw
      have h2 := Guard.comb_smul hvK hw (φ (embK c τ a))
      rw [← h a] at h2
      rw [hs a]
      exact (hbK _ (Guard.comb_tan hvK h1)).unique h1 h2
  unfold eigRank
  rw [key, hVr]

end GlobalTheory.BalProjInt

theorem GlobalTheory.BalProjInt.eigRank_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (𝔭 : PrimeSpectrum Γ(Y.X, U.1)), (chart U).base 𝔭 ∈ (interior Y : Set Y.X) → ∀ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ) = if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q := by
  intro E _ _ _ H Dw l Xo c Y _ _ _ U n v A hv hb hA 𝔭 _ τ
  exact GlobalTheory.BalProjInt.eigRank_field Y U n v A hv hb hA _ _ τ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsIntClosedLocalDomainStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_absIntClosedLocalDomain : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : T →+* Polynomial T)) (tw q i) := by
  first | (exact @GlobalTheory.EtC.HtpyLine.htpy_AIC) | (exact GlobalTheory.EtC.HtpyLine.htpy_AIC) | (intros; apply GlobalTheory.EtC.HtpyLine.htpy_AIC  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFieldsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_raynaudTangent_invariantFields : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  first | exact @GlobalTheory.RayBasis.exists_basis_isInv | exact GlobalTheory.RayBasis.exists_basis_isInv | (intros; apply GlobalTheory.RayBasis.exists_basis_isInv <;> assumption)
end

