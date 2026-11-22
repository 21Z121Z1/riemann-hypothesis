import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusStableGoodOpenOfWeightUnits
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.PointGroup

theorem isIntegrallyClosedIn_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

theorem exists_tensor_eq {R O M N : Type} [CommRing R] [CommRing O] [Algebra R O] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N]
    (B : M →ₗ[R] N →ₗ[R] R) (hB : Function.Surjective B) (φ : O ⊗[R] N →ₗ[O] O) :
    ∃ x : O ⊗[R] M, ∀ n, TensorProduct.rid R O ((B.flip n).baseChange O x) = φ (1 ⊗ₜ n) := by
  let b := Module.Free.chooseBasis R N
  choose s hs using fun i => hB (b.coord i)
  refine ⟨∑ i, φ (1 ⊗ₜ b i) ⊗ₜ s i, fun n => ?_⟩
  conv_rhs => rw [← b.sum_repr n]
  simp only [map_sum, LinearMap.baseChange_tmul, LinearMap.flip_apply, hs, TensorProduct.rid_tmul,
    TensorProduct.tmul_sum, Module.Basis.coord_apply, TensorProduct.tmul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul O (b.repr n i) ((1 : O) ⊗ₜ[R] b i), map_smul, algebraMap_smul]

theorem exists_lift {R Λ E : Type} [CommRing R] [CommRing Λ] [Ring E] [Algebra R E]
    (ψ : Λ →+* E) : ∃ ρ : R ⊗[ℤ] Λ →+* E, ∀ a, ρ (1 ⊗ₜ a) = ψ a :=
  ⟨(Algebra.TensorProduct.lift (algebraMap R E).toIntAlgHom ψ.toIntAlgHom
    fun a b => Algebra.commute_algebraMap_left a _).toRingHom, fun a => (Algebra.TensorProduct.lift_tmul _ _ _ 1 a).trans
      (by rw [map_one, one_mul]; rfl)⟩

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

theorem exists_form (hv : v.Integers O) (G : PDivGroup p O) (ζ : (PDivGroup.mu p O).Tate)
    (hζ : Function.Bijective fun a : ℤ_[p] => a • ζ) :
    ∃ B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p], (∀ s χ, pairing G O s χ = B s χ • ζ) ∧
      Function.Bijective B ∧ Function.Bijective B.flip := by
  haveI := isIntegrallyClosedIn_of_integers hv
  let z := LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ ζ) hζ
  refine ⟨(pairing G O).compr₂ z.symm.toLinearMap, fun s χ => (z.apply_symm_apply _).symm, ?_, ?_⟩
  · exact (LinearEquiv.congrRight (M := G.dual.Tate) z.symm).bijective.comp (G.pairing_bijective C)
  · exact (LinearEquiv.congrRight (M := G.Tate) z.symm).bijective.comp (G.pairing_flip_bijective C)

theorem finite_tate (hv : v.Integers O) (G : PDivGroup p O) : Module.Finite ℤ_[p] G.Tate :=
  haveI := isIntegrallyClosedIn_of_integers hv
  G.finite_tate C

theorem free_tate (hv : v.Integers O) (G : PDivGroup p O) : Module.Free ℤ_[p] G.Tate :=
  haveI := isIntegrallyClosedIn_of_integers hv
  G.free_tate C

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O]
  {ε : PreTilt O p} {hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε}

theorem lie_eq_zero (hv : v.Integers O) (H : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε)
    (G : PDivGroup p O) (y : G.Lie) (hy : ∀ χ, y (dlog G χ) = 0) : y = 0 := by
  obtain ⟨u₁, u₂, H⟩ := H
  obtain ⟨D, e, fil, lie, R⟩ := H G ℤ_[p] G.padicAction
  obtain ⟨B, hB, -, hB'⟩ := exists_form hv G _ (GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsEquiv hε).bijective
  have hE : ∀ s χ, GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing hε G s χ = B s χ := fun s χ =>
    (LinearEquiv.symm_apply_eq _).2 (hB s χ)
  have h0 : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.bQuot D (lie.symm y) = 0 := by
    funext j
    obtain ⟨χ, hχ⟩ := hB'.2 (LinearMap.proj j ∘ₗ e.toLinearMap)
    have h1 : ∀ s, B s χ = e s j := fun s => LinearMap.congr_fun hχ s
    have h := R.b_eq y χ
    rw [← dlog_eq_omegaMap, hy, mul_zero, GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO] at h
    simpa [hE, h1, Pi.single_apply, apply_ite] using h
  have h1 : lie.symm y = 0 := by
    have hk : LinearMap.ker (GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.bQuot D) = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
    exact LinearMap.ker_eq_bot'.1 hk _ h0
  exact lie.symm.map_eq_zero_iff.1 h1

theorem omega_eq_zero (H : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε)
    (G : PDivGroup p O) (w : G.omega) (hw : ∀ y : G.Lie, y w = 0) : w = 0 := by
  obtain ⟨u₁, u₂, H⟩ := H
  obtain ⟨D, e, fil, lie, R⟩ := H G.dual ℤ_[p] G.dual.padicAction
  have h : fil (omegaMap _ _ G.bidual.inv w) = 0 := Subtype.ext (funext fun j =>
    hw (LinearMap.proj j ∘ₗ D.Fil.subtype ∘ₗ fil.toLinearMap ∘ₗ omegaMap _ _ G.bidual.inv))
  have h2 := congrArg (omegaMap _ _ G.bidual.hom) (fil.map_eq_zero_iff.1 h)
  rwa [map_zero, ← LinearMap.comp_apply, ← omegaMap_comp, Iso.hom_inv_id, omegaMap_id] at h2

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] in

theorem hodgeTateLinear_dual_eq_zero_iff [Algebra ℤ_[p] O] (G : PDivGroup p O)
    (z : O ⊗[ℤ_[p]] G.dual.Tate) : G.dual.hodgeTateLinear z = 0 ↔ dlogLinear G z = 0 := by
  have h : G.dual.hodgeTateLinear z = omegaMap _ _ G.bidual.inv (dlogLinear G z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c χ =>
      rw [hodgeTateLinear_tmul, dlogLinear_tmul, map_smul, hodgeTate_apply, ← dlog_tateMap,
        dualHom_bidual_inv]
  rw [h]
  refine ⟨fun h0 => ?_, fun h0 => by rw [h0, map_zero]⟩
  have h2 := congrArg (omegaMap _ _ G.bidual.hom) h0
  rwa [map_zero, ← LinearMap.comp_apply, ← omegaMap_comp, Iso.hom_inv_id, omegaMap_id] at h2

omit [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] in

def KerIsLie [Algebra ℤ_[p] O] (G : PDivGroup p O)
    (B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]) : Prop :=
  ∀ x : O ⊗[ℤ_[p]] G.Tate, G.hodgeTateLinear x = 0 ↔ ∃ (c : O) (y : G.Lie), c ≠ 0 ∧
    ∀ χ, c * (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) = y (dlog G χ)

variable [Algebra ℤ_[p] O]

omit [IsDomain O] in

theorem eq_id_of_tateMap (SW : GlobalTheory.Published.ScholzeWeinsteinB) (hv : v.Integers O) {G : PDivGroup p O}
    (φ : G ⟶ G) (h : ∀ t, tateMap G G O φ t = t) : φ = 𝟙 G :=
  ((SW p C v O hv).1 G G LinearMap.id fun x hx => by rwa [LinearMap.baseChange_id]).unique
    (LinearMap.ext h) rfl

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in

theorem exists_ker_of_lie (hv : v.Integers O) {G : PDivGroup p O}
    {B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]} (hB : Function.Surjective B)
    (hk : KerIsLie G B) (y : G.Lie) : ∃ x, G.hodgeTateLinear x = 0 ∧
      ∀ χ, (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) = y (dlog G χ) := by
  haveI := finite_tate hv G.dual
  haveI := free_tate hv G.dual
  obtain ⟨x, hx⟩ := exists_tensor_eq B hB (y ∘ₗ dlogLinear G)
  have hx' : ∀ χ, (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) = y (dlog G χ) :=
    fun χ => by rw [hx, LinearMap.comp_apply, dlogLinear_tmul, one_smul]
  exact ⟨x, (hk x).2 ⟨1, y, one_ne_zero, fun χ => by rw [one_mul, hx']⟩, hx'⟩

theorem exists_pol (SW : GlobalTheory.Published.ScholzeWeinsteinB) (hv : v.Integers O)
    (H : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε) (G : PDivGroup p O) (ζ : (PDivGroup.mu p O).Tate)
    (B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]) (hB : ∀ s χ, pairing G O s χ = B s χ • ζ)
    (hB1 : Function.Surjective B) (hB2 : Function.Bijective B.flip) (hk : KerIsLie G B)
    (β : LinearMap.BilinForm ℤ_[p] G.Tate) (hβ : Function.Bijective β.flip)
    (hL : ∀ z, G.hodgeTateLinear z = 0 ↔
      ∀ x, G.hodgeTateLinear x = 0 → β.baseChange O x z = 0) :
    ∃ pol : G ≅ G.dual, ∀ s t, pairing G O s (tateMap G G.dual O pol.hom t) = β s t • ζ := by
  let f : G.Tate ≃ₗ[ℤ_[p]] G.dual.Tate :=
    (LinearEquiv.ofBijective β.flip hβ).trans (LinearEquiv.ofBijective B.flip hB2).symm
  have hf : ∀ s t, B s (f t) = β s t := fun s t =>
    LinearMap.congr_fun ((LinearEquiv.ofBijective B.flip hB2).apply_symm_apply (β.flip t)) s
  have h1 : ∀ x (d : O) t, β.baseChange O x (d ⊗ₜ t) =
      d * (TensorProduct.rid ℤ_[p] O) ((B.flip (f t)).baseChange O x) := fun x d t => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, mul_add]
    | tmul a s =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.flip_apply, hf,
        TensorProduct.rid_tmul, mul_smul_comm, mul_comm]
  have h2 : ∀ x (c : O) (y : G.Lie),
      (∀ χ, c * (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) = y (dlog G χ)) →
      ∀ z, c * β.baseChange O x z = y (dlogLinear G (f.toLinearMap.baseChange O z)) :=
    fun x c y h z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add, hz, hw, mul_add]
      | tmul d t =>
        rw [h1, LinearMap.baseChange_tmul, dlogLinear_tmul, map_smul, ← h, smul_eq_mul,
          mul_left_comm]
        rfl
  have h3 : ∀ z, G.hodgeTateLinear z = 0 ↔
      G.dual.hodgeTateLinear (f.toLinearMap.baseChange O z) = 0 := fun z => by
    rw [hodgeTateLinear_dual_eq_zero_iff]
    refine ⟨fun hz => omega_eq_zero H G _ fun y => ?_, fun hz => (hL z).2 fun x hx => ?_⟩
    · obtain ⟨x, hx, hx'⟩ := exists_ker_of_lie hv hB1 hk y
      rw [← h2 x 1 y (fun χ => by rw [one_mul, hx']), (hL z).1 hz x hx, mul_zero]
    · obtain ⟨c, y, hc, h⟩ := (hk x).1 hx
      have := h2 x c y h z
      rw [hz, map_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hc
  obtain ⟨φ, hφ, -⟩ := (SW p C v O hv).1 G G.dual f.toLinearMap fun x hx => (h3 x).1 hx
  obtain ⟨ψ, hψ, -⟩ := (SW p C v O hv).1 G.dual G f.symm.toLinearMap fun x hx => (h3 _).2 (by
    rwa [← LinearMap.comp_apply (f.toLinearMap.baseChange O), ← LinearMap.baseChange_comp,
      LinearEquiv.comp_symm, LinearMap.baseChange_id])
  refine ⟨⟨φ, ψ, eq_id_of_tateMap SW hv _ fun t => ?_, eq_id_of_tateMap SW hv _ fun t => ?_⟩,
    fun s t => ?_⟩
  · rw [tateMap_comp, hφ, hψ]; exact f.symm_apply_apply t
  · rw [tateMap_comp, hφ, hψ]; exact f.apply_symm_apply t
  · rw [hφ, hB, ← hf]; rfl

theorem exists_lie_bijective (SW : GlobalTheory.Published.ScholzeWeinsteinB) (hv : v.Integers O)
    (H : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε) (G G₁ : PDivGroup p O)
    (ζ : (PDivGroup.mu p O).Tate) (hζ : Function.Injective fun a : ℤ_[p] => a • ζ)
    (B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]) (hB : ∀ s χ, pairing G O s χ = B s χ • ζ)
    (hB1 : Function.Surjective B) (hk : KerIsLie G B)
    (ι : G₁.Tate →ₗ[ℤ_[p]] G.Tate) (r : G.Tate →ₗ[ℤ_[p]] G₁.Tate) (hr : ∀ s, r (ι s) = s)
    (h1 : ∀ x, G₁.hodgeTateLinear x = 0 ↔ G.hodgeTateLinear (ι.baseChange O x) = 0)
    (h2 : ∀ x, G.hodgeTateLinear x = 0 → ι.baseChange O (r.baseChange O x) = x) :
    ∃ i : G₁ ⟶ G, tateMap G₁ G O i = ι ∧ Function.Bijective (lieMap G₁ G i) := by
  obtain ⟨i, hi, -⟩ := (SW p C v O hv).1 G₁ G ι fun x hx => (h1 x).1 hx
  obtain ⟨ρ, hρ, -⟩ := (SW p C v O hv).1 G G₁ r fun x hx => (h1 _).2 (by rwa [h2 x hx])
  have h3 : i ≫ ρ = 𝟙 G₁ := eq_id_of_tateMap SW hv _ fun t => by rw [tateMap_comp, hi, hρ, hr]
  refine ⟨i, hi, Function.bijective_iff_has_inverse.2 ⟨lieMap G G₁ ρ, fun y => ?_, fun y => ?_⟩⟩
  · rw [← LinearMap.comp_apply, ← lieMap_comp, h3, lieMap_id, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← lieMap_comp]
    obtain ⟨x, hx, hx'⟩ := exists_ker_of_lie hv hB1 hk y
    refine sub_eq_zero.1 (lie_eq_zero hv H G _ fun χ => ?_)
    have h4 : B.flip (tateMap _ _ O (dualHom G G (ρ ≫ i)) χ) = B.flip χ ∘ₗ ι ∘ₗ r :=
      LinearMap.ext fun s => hζ (by
        have := pairing_tateMap (ρ ≫ i) s χ
        rw [hB, hB, tateMap_comp, hi, hρ] at this
        exact this.symm)
    rw [LinearMap.sub_apply, lieMap_apply, ← dlog_tateMap, ← hx', ← hx', h4,
      LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply,
      LinearMap.comp_apply, h2 x hx, sub_self]

omit [IsDomain O] in

theorem exists_action (SW : GlobalTheory.Published.ScholzeWeinsteinB) (hv : v.Integers O) (G : PDivGroup p O)
    {Λ : Type} [CommRing Λ] (α : Λ →+* Module.End ℤ_[p] G.Tate)
    (h : ∀ a x, G.hodgeTateLinear x = 0 → G.hodgeTateLinear ((α a).baseChange O x) = 0) :
    ∃ ρ : Action (ℤ_[p] ⊗[ℤ] Λ) G, ∀ a, ρ.onTate O (1 ⊗ₜ a) = α a := by
  have hex := fun a => (SW p C v O hv).1 G G (α a) (h a)
  choose φ hφ hu using hex
  let ψ : Λ →+* End G :=
    { toFun := φ
      map_one' := (hu 1 _ (by rw [map_one]; rfl)).symm
      map_mul' := fun a b => (hu (a * b) (φ b ≫ φ a) (by
        rw [map_mul, ← hφ a, ← hφ b]; rfl)).symm
      map_zero' := (hu 0 _ (by rw [map_zero]; exact map_zero _)).symm
      map_add' := fun a b => (hu (a + b) (φ a + φ b) (by
        rw [map_add, ← hφ a, ← hφ b]; exact map_add _ _ _)).symm }
  obtain ⟨ρ, hρ⟩ := exists_lift (R := ℤ_[p]) ψ
  exact ⟨ρ, fun a => by rw [Action.onTate_apply, hρ]; exact hφ a⟩

end GlobalTheory.PointGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoCotMapOfIsOpenImmersion
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusCot

open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open GlobalTheory.Conormal GlobalTheory.SS.TorusSlice

def derOpen {S X Y : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} {π' : Y ⟶ S} {e' : S ⟶ Y} {F : S.Modules}
    (φ : Y ⟶ X) [IsOpenImmersion φ] (w : φ ≫ π = π') (we : e' ≫ φ = e) (D : Der π e F) : Der π' e' F :=
  have hle : ∀ {W : Y.Opens} {V : S.Opens}, V ≤ e' ⁻¹ᵁ W → V ≤ e ⁻¹ᵁ (φ ''ᵁ W) := fun {W V} h =>
    (le_preimage_of_comp we).1 (by rwa [φ.preimage_image_eq])
  have hinj : ∀ W : Y.Opens, Function.Injective (φ.appLE (φ ''ᵁ W) W (φ.preimage_image_eq W).ge) := fun W => by
    rw [← Scheme.Hom.appIso_hom']
    exact (ConcreteCategory.bijective_of_isIso _).1
  have hinv : ∀ (W : Y.Opens) (a : Γ(Y, W)),
      φ.appLE (φ ''ᵁ W) W (φ.preimage_image_eq W).ge ((φ.appIso W).inv a) = a := fun W a => by
    rw [← Scheme.Hom.appIso_hom']
    exact congrArg (fun ψ => ψ.hom a) (φ.appIso W).inv_hom_id
  { app {W V} h := (D.app (hle h)).comp (φ.appIso W).inv.hom.toAddMonoidHom
    res_app h h' f := D.res_app _ h' _
    app_res {W W' V} h k f := by
      refine (congrArg (D.app _) (hinj W' ?_)).trans (D.app_res _ (φ.image_mono k) _)
      refine (hinv _ _).trans ?_
      rw [appLE_resG, ← resG_appLE φ k (φ.preimage_image_eq W).ge]
      exact congrArg _ (hinv _ _).symm
    app_mul {W V} h f g := by
      refine (congrArg (D.app _) (map_mul (φ.appIso W).inv.hom f g)).trans ((D.app_mul _ _ _).trans ?_)
      rw [← appLE_appLE we (φ.preimage_image_eq W).ge h, ← appLE_appLE we (φ.preimage_image_eq W).ge h]
      erw [hinv, hinv]
      rfl
    app_base {W V U} h k a := by
      have k' : φ ''ᵁ W ≤ π ⁻¹ᵁ U :=
        (φ.image_mono ((le_preimage_of_comp w).2 k)).trans (φ.image_preimage_le _)
      refine (congrArg (D.app _) (hinj W ?_)).trans (D.app_base _ k' a)
      exact (hinv _ _).trans (appLE_appLE w _ _ _ a).symm }

theorem isFrame_append {S : Scheme.{0}} {F F₁ F₂ : S.Modules} {p₁ : F₁ ⟶ F} {p₂ : F₂ ⟶ F} {i₁ : F ⟶ F₁}
    {i₂ : F ⟶ F₂} (h : i₁ ≫ p₁ + i₂ ≫ p₂ = 𝟙 _) (h₁ : p₁ ≫ i₁ = 𝟙 _) (h₂ : p₂ ≫ i₂ = 𝟙 _) (h₃ : p₁ ≫ i₂ = 0)
    (h₄ : p₂ ≫ i₁ = 0) {U : S.Opens} {n m : ℕ} {e₁ : Fin n → Γ(F₁, U)} {e₂ : Fin m → Γ(F₂, U)}
    (he₁ : IsFrame e₁) (he₂ : IsFrame e₂) :
    IsFrame (Fin.append (fun i => p₁.app U (e₁ i)) fun j => p₂.app U (e₂ j)) := by
  let ψ (V : S.Opens) : (Γ(F₁, V) × Γ(F₂, V)) ≃ₗ[Γ(S, V)] Γ(F, V) :=
    LinearEquiv.ofBijective ((QCoh.appLinear p₁ V).coprod (QCoh.appLinear p₂ V)) ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨a, b⟩ hab
      change p₁.app V a + p₂.app V b = 0 at hab
      have a₁ := congrArg (i₁.app V) hab
      have a₂ := congrArg (i₂.app V) hab
      rw [map_add, map_zero, QCoh.app_app, QCoh.app_app] at a₁ a₂
      rw [h₁, h₄] at a₁
      rw [h₃, h₂] at a₂
      ext
      · simpa using a₁
      · simpa using a₂, fun c => ⟨(i₁.app V c, i₂.app V c), congr(($h).app V c)⟩⟩
  refine isFrame_of_basis (fun V k => (((he₁.basis k).prod (he₂.basis k)).map (ψ V)).reindex finSumFinEquiv)
    fun V k i => ?_
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_apply]
  rcases i with i | i
  · change p₁.app V _ + p₂.app V _ = _
    simp [app_resM]
  · change p₁.app V _ + p₂.app V _ = _
    simp [app_resM]

section Geo

variable {S : Scheme.{0}} {T G B Y : Over S} [GrpObj T] [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
  [IsMonHom u] {j : Y ⟶ G} {σ : Y ⟶ T}

end Geo

end GlobalTheory.TorusCot

namespace GlobalTheory.TorusPart

open GlobalTheory.TorusCot GlobalTheory.QCoh

end GlobalTheory.TorusPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyDegreeKilledByPrimeToPHarrisTaylor
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel.PrimeToP

theorem isIsogDeg_killedBy : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s), (∀ c : 𝓞 D.F, c ≠ 0 → GlobalTheory.IwLevel.IsIsogDeg (o.act.act (algebraMap (𝓞 D.F) D.O c)) ((Algebra.norm ℤ c).natAbs ^ (D.m * D.n))) → ∀ (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (K : Over S) (i : K ⟶ o.A), Mono i → (∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) x) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) (Ideal.absNorm 𝔟 ^ (D.m * D.n)) := by
  intro p _ D R _ b N S s o _hdeg 𝔟 h𝔟 K i hi hK
  obtain ⟨K', i', hi', hfin, het, hK'⟩ := GlobalTheory.T.killed_by_ideal_finite_etale p D R b N S s o 𝔟 h𝔟
  have hne : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [bot_sup_eq] at h𝔟
    have h1 := congrArg Ideal.absNorm h𝔟
    rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top] at h1
    have h2 : Algebra.norm ℤ ((p : ℤ) : 𝓞 D.F) = (p : ℤ) ^ Module.finrank ℤ (𝓞 D.F) := by
      rw [← Algebra.norm_algebraMap]; rfl
    rw [Int.cast_natCast] at h2
    rw [h2, Int.natAbs_pow, Int.natAbs_natCast] at h1
    have hp := (Fact.out : p.Prime).one_lt
    have hr : 0 < Module.finrank ℤ (𝓞 D.F) := Module.finrank_pos
    have := Nat.one_lt_pow hr.ne' hp
    omega
  have hd : 1 ≤ Ideal.absNorm 𝔟 ^ (D.m * D.n) :=
    Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (fun h => hne (Ideal.absNorm_eq_zero_iff.1 h)))
  obtain ⟨u, hu⟩ : GlobalTheory.IwLevel.InSub i' i := (hK' K i).2 ((hK K i).1 ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨v, hv⟩ : GlobalTheory.IwLevel.InSub i i' := (hK K' i').2 ((hK' K' i').1 ⟨𝟙 _, Category.id_comp _⟩)
  have : IsIso u := ⟨⟨v, by rw [← cancel_mono i, Category.assoc, hv, hu, Category.id_comp],
    by rw [← cancel_mono i', Category.assoc, hu, hv, Category.id_comp]⟩⟩
  have h3 := GlobalTheory.T.isogeny_degree_of_point_count o.A K' i' hi' hfin het _ hd fun k _ _ t => by
    rw [← GlobalTheory.T.harrisTaylor_card_killed_by_ideal_eq_absNorm_pow p D R b N S s o 𝔟 h𝔟 k t]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => hK' _ y)
  have h4 := (GlobalTheory.IwLevel.IsIsogDeg.of_isIso u).comp h3
  rwa [_root_.one_mul, toUnit_unique (u ≫ toUnit K') (toUnit K)] at h4

end GlobalTheory.IwLevel.PrimeToP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenComapProdLev
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.ProdOpen

open Filter Topology

variable {D : D7}

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem inBasis_apply {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).1 i j = cpt w ((β⁻¹ * x * β).1 (finCongr h i) (finCongr h j)) := rfl

theorem inBasis_mem_KO {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (hx : x ∈ St β) (w : Pl D.host.E) :
    inBasis rfl β w x ∈ KO (Kw w) (Fin n) := by
  obtain ⟨y, rfl⟩ := hx
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  have hm : ∀ z : GL (Fin n) (Lev.EAf D), z ∈ ({Formalism.L2.DIV.intGL _ _ n y, (Formalism.L2.DIV.intGL _ _ n y)⁻¹} : Set _) →
      ∀ a b, cpt w (z.1 a b) ∈ Formalism.UG.Ov D.host.E w := by
    intro z hz a b
    refine (mem_OA_iff _).1 ?_ w
    rcases hz with rfl | rfl
    · exact (y.1 a b).2
    · rw [← map_inv]; exact ((y⁻¹).1 a b).2
  have e1 : β⁻¹ * Formalism.L2.DIV.frGL β y * β = Formalism.L2.DIV.intGL _ _ n y := by
    simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  have e2 : β⁻¹ * (Formalism.L2.DIV.frGL β y)⁻¹ * β = (Formalism.L2.DIV.intGL _ _ n y)⁻¹ := by
    rw [← e1]; group
  refine mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [inBasis_apply, e1]; exact hm _ (Or.inl rfl) _ _
  · rw [← map_inv, inBasis_apply, e2]; exact hm _ (Or.inr rfl) _ _

theorem tendsto_inBasis_val (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) :
    Tendsto (fun κ : GA D V => ((inBasis h β w (Lev.finE V κ)).1 : Matrix (Fin n') (Fin n') (Kw w))) (𝓝 1) (𝓝 1) := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : Continuous (finHom V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (GlobalTheory.LocalData.norm_resChar_lt_one w)
  have hN : Formalism.MainNotions.S.Loc.resChar w ^ k ≠ 0 := pow_ne_zero _ (GlobalTheory.LocalData.resChar_prime w).ne_zero
  filter_upwards [eventually_cong_mat β hN hf (map_one _)] with κ ⟨z, hz, e⟩
  change (β⁻¹ * Lev.finE V κ * β).1 - 1 = _ at e
  have e2 := congr_fun (congr_fun e (finCongr h i)) (finCongr h j)
  rw [Matrix.sub_apply, Matrix.smul_apply, sub_eq_iff_eq_add] at e2
  have e3 : cpt w ((1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) (finCongr h i) (finCongr h j)) =
      (1 : Matrix (Fin n') (Fin n') (Kw w)) i j := by
    simp only [Matrix.one_apply, (finCongr h).injective.eq_iff]
    split_ifs <;> simp
  have hz1 : ‖cpt w (z (finCongr h i) (finCongr h j))‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.2 ((mem_OA_iff _).1 (hz _ _) w)
  rw [dist_eq_norm, inBasis_apply, e2, map_add, e3, add_sub_cancel_right, map_nsmul, nsmul_eq_mul, norm_mul,
    Nat.cast_pow, norm_pow]
  calc ‖((Formalism.MainNotions.S.Loc.resChar w : ℕ) : Kw w)‖ ^ k * ‖cpt w (z (finCongr h i) (finCongr h j))‖
      ≤ ‖((Formalism.MainNotions.S.Loc.resChar w : ℕ) : Kw w)‖ ^ k * 1 := by gcongr
    _ < ε := by rwa [mul_one]

theorem tendsto_inBasis (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) :
    Tendsto (fun κ : GA D V => inBasis h β w (Lev.finE V κ)) (𝓝 1) (𝓝 1) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
  have hinv : Tendsto (fun κ : GA D V => κ⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using (continuous_inv.tendsto (1 : GA D V))
  have h2 : Tendsto (fun κ : GA D V => ((inBasis h β w (Lev.finE V κ))⁻¹).1) (𝓝 1) (𝓝 1) := by
    have := (tendsto_inBasis_val V h β w).comp hinv
    refine this.congr fun κ => ?_
    simp only [Function.comp_apply, map_inv]
  have h3 := (tendsto_inBasis_val V h β w).prodMk_nhds (MulOpposite.continuous_op.tendsto _ |>.comp h2)
  convert h3 using 2
  · ext <;> simp [Units.embedProduct]
  · rw [map_one]; rfl

theorem isOpen_comap_prodLev : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ}
    (h : ∀ w, n' w = V.rank) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))),
    (∀ w, IsOpen (K w : Set (GL (Fin (n' w)) (Kw w.1)))) →
      IsOpen (((prodLev β P h K).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  intro D V β P n' h K hK
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hP : ∀ w : P, ∀ᶠ κ in 𝓝 (1 : GA D V), inBasis (h w) β w (Lev.finE V κ) ∈ K w := fun w =>
    tendsto_inBasis V (h w) β w.1 ((hK w).mem_nhds (one_mem _))
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β ∅, Filter.eventually_all.2 hP] with κ hh h3
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 h3,
    Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => inBasis_mem_KO β _ hh.2.1 w'⟩

end GlobalTheory.FunObj.ProdOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteModuleIrreducibleOfIrreducibleUnitaryRepStatement
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFiniteModule_irreducible_of_irreducible_unitaryRep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ N : Submodule ℂ D, (∀ a b, ∀ x ∈ N, E a b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  first | exact @GlobalTheory.KFinIrr.kMod_irred | exact GlobalTheory.KFinIrr.kMod_irred | (intros; apply GlobalTheory.KFinIrr.kMod_irred <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCartierOfLocallyPrincipalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_cartier_of_locally_principal' : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData), (∀ y : Y, ∃ (W : Y.affineOpens) (a : Γ(Y, W.1)), y ∈ W.1 ∧ a ∈ nonZeroDivisors Γ(Y, W.1) ∧ I.ideal W = Ideal.span {a}) → Nonempty (Cartier I) := by
  first | exact @GlobalTheory.CompHS.nonempty_cartier_of_locally_principal | exact GlobalTheory.CompHS.nonempty_cartier_of_locally_principal | (intros; apply GlobalTheory.CompHS.nonempty_cartier_of_locally_principal <;> assumption)
end

