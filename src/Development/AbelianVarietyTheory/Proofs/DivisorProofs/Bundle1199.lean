import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1135
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeKilledByNegativeNoncompactRootsStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_killed_by_negative_noncompact_roots : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : ℕ) (s : Bool), (∀ a : Fin n, ε a = if (a : ℕ) < p then s else !s) → StrictAnti lam → IsDS ε lam π → ∀ v ∈ lowKSub ε lam π, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0} π v → ∀ a b : Fin n, ε a ≠ ε b → b < a → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, X + Complex.I • Y = Matrix.single a b 1 → dRep π X v + Complex.I • dRep π Y v = 0 := by
  first | exact @GlobalTheory.LowestKilled.lowK_killed | exact GlobalTheory.LowestKilled.lowK_killed | (intros; apply GlobalTheory.LowestKilled.lowK_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliserStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_centralizer_regular_twistedCentraliser : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r), 0 < r → regular₂ G γ → IsNrm G r γ δ z → (Subgroup.centralizer {γ}).map (carry G r z) = GlobalTheory.BCT.twCent (sigG G r) δ := by
  first | (exact @GlobalTheory.CarryCent.map_centralizer_carry) | (exact GlobalTheory.CarryCent.map_centralizer_carry) | (intros; apply GlobalTheory.CarryCent.map_centralizer_carry  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsCompEqOfFunctionFieldMapsAgreeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maps_comp_eq_of_functionField_maps_agree : ∀ (F : Type) [Field F] (X Y : Var F) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), (ratOf X).IsHom (ratOf Y) φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → W.p₁ ≫ f = W.p₂ ≫ f := by
  first | exact @GlobalTheory.FlagPush.Dbl.p_comp_eq_of_isHom | exact GlobalTheory.FlagPush.Dbl.p_comp_eq_of_isHom | (intros; apply GlobalTheory.FlagPush.Dbl.p_comp_eq_of_isHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFibreProductStableLatticeChainLine
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreLine

theorem cancel_left {O : Type} [CommRing O] {a b c : ℕ} {A : Matrix (Fin a) (Fin b) O}
    (hA : Function.Injective A.mulVec) {X Y : Matrix (Fin b) (Fin c) O} (h : A * X = A * Y) : X = Y := by
  refine Matrix.ext_of_mulVec_single fun j => hA ?_
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem cancel_left₂ {O : Type} [CommRing O] {a a' b c : ℕ} {A : Matrix (Fin a) (Fin b) O}
    {A' : Matrix (Fin a') (Fin b) O} (hA : ∀ v, A *ᵥ v = 0 → A' *ᵥ v = 0 → v = 0)
    {X Y : Matrix (Fin b) (Fin c) O} (h : A * X = A * Y) (h' : A' * X = A' * Y) : X = Y := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  refine sub_eq_zero.mp (hA _ ?_ ?_)
  · rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, sub_self]
  · rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h', sub_self]

theorem solve {O : Type} [CommRing O] {a b c : ℕ} (A : Matrix (Fin a) (Fin b) O) (B : Matrix (Fin a) (Fin c) O)
    (h : ∀ v, ∃ w, A *ᵥ w = B *ᵥ v) : ∃ S : Matrix (Fin b) (Fin c) O, B = A * S := by
  choose w hw using h
  refine ⟨Matrix.of fun i j => w (Pi.single j 1) i, Matrix.ext_of_mulVec_single fun j => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← hw]
  congr 1
  rw [Matrix.mulVec_single_one]
  rfl

theorem mkRep {Γ O : Type} [Group Γ] [CommRing O] {a a' m : ℕ} (A : Matrix (Fin a) (Fin m) O)
    (A' : Matrix (Fin a') (Fin m) O) (ρ : Γ →* GL (Fin a) O) (ρ' : Γ →* GL (Fin a') O)
    (hA : ∀ v, A *ᵥ v = 0 → A' *ᵥ v = 0 → v = 0)
    (hst : ∀ g v, ∃ w, A *ᵥ w = (ρ g : Matrix (Fin a) (Fin a) O) *ᵥ (A *ᵥ v) ∧
      A' *ᵥ w = (ρ' g : Matrix (Fin a') (Fin a') O) *ᵥ (A' *ᵥ v)) :
    ∃ r' : Γ →* GL (Fin m) O, Tw r' ρ A ∧ Tw r' ρ' A' := by
  choose w hw using hst
  let M : Γ → Matrix (Fin m) (Fin m) O := fun g => Matrix.of fun i j => w g (Pi.single j 1) i
  have hM : ∀ g j, M g *ᵥ Pi.single j 1 = w g (Pi.single j 1) := fun g j => by
    rw [Matrix.mulVec_single_one]
    rfl
  have k1 : ∀ g, A * M g = (ρ g : Matrix (Fin a) (Fin a) O) * A := fun g =>
    Matrix.ext_of_mulVec_single fun j => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, (hw g _).1]
  have k2 : ∀ g, A' * M g = (ρ' g : Matrix (Fin a') (Fin a') O) * A' := fun g =>
    Matrix.ext_of_mulVec_single fun j => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, (hw g _).2]
  let f : Γ →* Matrix (Fin m) (Fin m) O :=
    { toFun := M
      map_one' := cancel_left₂ hA (by rw [k1, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
        (by rw [k2, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
      map_mul' := fun g h => cancel_left₂ hA
        (by rw [k1, ← Matrix.mul_assoc, k1, Matrix.mul_assoc, k1, ← Matrix.mul_assoc, map_mul, Units.val_mul])
        (by rw [k2, ← Matrix.mul_assoc, k2, Matrix.mul_assoc, k2, ← Matrix.mul_assoc, map_mul, Units.val_mul]) }
  refine ⟨f.toHomUnits, fun g => ?_, fun g => ?_⟩
  · rw [MonoidHom.coe_toHomUnits]
    exact k1 g
  · rw [MonoidHom.coe_toHomUnits]
    exact k2 g

theorem rank_map {O F : Type} [CommRing O] [Field F] (f : O →+* F) {a b : ℕ} (A : Matrix (Fin a) (Fin b) O)
    (B : Matrix (Fin b) (Fin a) O) (h : A * B = 1) : (A.map f).rank = a ∧ (B.map f).rank = a :=
  rank_of_mul_eq_one _ _ (by rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)])

theorem fibre_line : ∀ {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (r : Γ →* GL (Fin n) O) (χ : Γ →* Oˣ) (Ac As : Matrix (Fin n) (Fin n) O) (ρc ρs : Γ →* GL (Fin n) O) (x : Fin n → O), Function.Injective Ac.mulVec → Function.Injective As.mulVec → Tw ρc r Ac → Tw ρs r As → (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) → (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (∀ g, ∃ u, Ac *ᵥ u = (r g : Matrix (Fin n) (Fin n) O) *ᵥ x - fun a => (χ g : O) * x a) → ∃ (r2 : Γ →* GL (Fin (n + 1)) O) (B B' : Matrix (Fin n) (Fin (n + 1)) O) (C : Matrix (Fin 1) (Fin (n + 1)) O) (E : Matrix (Fin (n + 1)) (Fin n) O), Tw r2 r B ∧ Tw r2 ρs B' ∧ Tw r2 (GlobalTheory.TripleGal.rk1 χ) C ∧ Tw ρc r2 E ∧ B * E = Ac ∧ C * E = 0 ∧ B = As * B' ∧ (E.map (residue O)).rank = n ∧ (C.map (residue O)).rank = 1 ∧ (B'.map (residue O)).rank = n ∧ ∀ v, B *ᵥ v = 0 → C *ᵥ v = 0 → v = 0 := by
  intro Γ O _ _ _ _ n r χ Ac As ρc ρs x hAc hAs htc hts h1 h2 h3 h4
  let B : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun i j => Fin.lastCases (x i) (fun j => Ac i j) j
  let Cm : Matrix (Fin 1) (Fin (n + 1)) O := Matrix.of fun _ j => Fin.lastCases (1 : O) (fun _ => 0) j
  let E : Matrix (Fin (n + 1)) (Fin n) O := Matrix.of fun i j => if i = j.castSucc then 1 else 0
  let P : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun i j => Fin.lastCases (0 : O) (fun j => if i = j then 1 else 0) j
  let e : Matrix (Fin (n + 1)) (Fin 1) O := Matrix.of fun _ _ => 1
  have hB : ∀ v, B *ᵥ v = Ac *ᵥ (fun j => v j.castSucc) + v (Fin.last n) • x := fun v => by
    funext i
    simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  have hC : ∀ v, Cm *ᵥ v = fun _ => v (Fin.last n) := fun v => by
    funext i
    simp [Cm, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  have hBs : ∀ (u : Fin n → O) (c : O), B *ᵥ (Fin.snoc u c : Fin (n + 1) → O) = Ac *ᵥ u + c • x := fun u c => by
    rw [hB]
    simp
  have hBE : B * E = Ac := by
    ext i k
    simp [B, E, Matrix.mul_apply]
  have hCE : Cm * E = 0 := by
    ext i k
    simp [Cm, E, Matrix.mul_apply]
  have hPE : P * E = 1 := by
    ext i k
    simp [P, E, Matrix.mul_apply, Matrix.one_apply]
  have hCe : Cm * e = 1 := by
    ext i k
    rw [Subsingleton.elim i k]
    simp [Cm, e, Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hinj : ∀ v, B *ᵥ v = 0 → Cm *ᵥ v = 0 → v = 0 := fun v hb hc => by
    have hl : v (Fin.last n) = 0 := by
      rw [hC] at hc
      exact congrFun hc 0
    rw [hB, hl, zero_smul, add_zero] at hb
    have h0 : (fun j : Fin n => v j.castSucc) = 0 := hAc (by rw [hb, Matrix.mulVec_zero])
    funext j
    refine Fin.lastCases hl (fun j => congrFun h0 j) j
  have hr : ∀ g, (GlobalTheory.TripleGal.rk1 χ g : Matrix (Fin 1) (Fin 1) O) = Matrix.scalar (Fin 1) (χ g : O) := fun _ => rfl
  obtain ⟨r2, hr2B, hr2C⟩ := mkRep B Cm r (GlobalTheory.TripleGal.rk1 χ) hinj (fun g v => by
    obtain ⟨u, hu⟩ := h4 g
    have hu' : (r g : Matrix (Fin n) (Fin n) O) *ᵥ x = Ac *ᵥ u + (χ g : O) • x := by
      rw [hu]
      exact (sub_add_cancel _ _).symm
    refine ⟨Fin.snoc ((ρc g : Matrix (Fin n) (Fin n) O) *ᵥ (fun j => v j.castSucc) + v (Fin.last n) • u)
      ((χ g : O) * v (Fin.last n)), ?_, ?_⟩
    · rw [hBs, hB, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, htc g,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hu', smul_add, smul_smul, mul_comm, add_assoc]
    · rw [hC, hC, hr]
      funext i
      simp [Matrix.mulVec_diagonal])
  obtain ⟨B', hB'⟩ := solve As B (fun v => by
    obtain ⟨w0, hw0⟩ := h2
    obtain ⟨w1, hw1⟩ := h3 (fun j => v j.castSucc)
    exact ⟨w1 + v (Fin.last n) • w0, by rw [hB, Matrix.mulVec_add, Matrix.mulVec_smul, hw0, hw1]⟩)
  obtain ⟨S, hS⟩ := solve B' (1 : Matrix (Fin n) (Fin n) O) (fun v => by
    obtain ⟨u, c, huc⟩ := h1 v
    refine ⟨Fin.snoc u c, hAs ?_⟩
    rw [Matrix.one_mulVec, Matrix.mulVec_mulVec, ← hB', hBs, huc]
    rfl)
  refine ⟨r2, B, B', Cm, E, hr2B, fun g => cancel_left hAs ?_, hr2C, fun g => cancel_left₂ hinj ?_ ?_, hBE, hCE, hB',
    (rank_map _ P E hPE).2, (rank_map _ Cm e hCe).1, (rank_map _ B' S hS.symm).1, hinj⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hB', hr2B g, hts g, Matrix.mul_assoc, ← hB']
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBE, hr2B g, Matrix.mul_assoc, hBE, htc g]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hCE, hr2C g, Matrix.mul_assoc, hCE, Matrix.zero_mul, Matrix.mul_zero]

end GlobalTheory.FibreLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixIntegralIntegrableLinear
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

noncomputable section
namespace GlobalTheory.GamMul

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem box_eq_standard_box (p q : ℕ) (c : kˣ) :
    box p q c = (GlobalTheory.LocMod.Inhab.box (Fin p) (Fin q) c : Set (Matrix (Fin p) (Fin q) k)) := rfl

theorem box_mono (p q : ℕ) {c d : kˣ} (h : valuation k (c : k) ≤ valuation k (d : k)) :
    box p q c ⊆ box p q d := fun _ hx i j => (hx i j).trans h

section Meas
variable [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure]

end Meas

end GlobalTheory.GamMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSameDoubleCosetOfHasElementaryDivisorsDefinitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_sameDoubleCoset_of_hasElementaryDivisors_definiteUnitary : ∀ (D : D7) [IsCMField D.host.E] (n : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (x y : UA D.host.E n), x ∈ locU n P → y ∈ locU n P →
    HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P y) →
    ∃ k₁ ∈ KP (D := D) n P, ∃ k₂ ∈ KP (D := D) n P, y = k₁ * x * k₂ := by
  first | exact @GlobalTheory.LocalCartan.doubleCoset_of_hasDiv | exact GlobalTheory.LocalCartan.doubleCoset_of_hasDiv | (intros; apply GlobalTheory.LocalCartan.doubleCoset_of_hasDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorCongruenceOfSupportedAtInfinityStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    ∀ w : AF F ⊗[F] E, At (evI F) w → w ∈ CE F E N := by
  first | exact @GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf | exact GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf | (intros; apply GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinOrdLeOrdAdd
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair.Place

variable {k K : Type} [Field k] [Field K] {c : k →+* K}

theorem ord_eq_zero_iff (E : Place c) {f : K} (hf : f ≠ 0) :
    E.ord f = 0 ↔ f ∈ E.ring ∧ f⁻¹ ∈ E.ring := by
  rw [← E.ord_nonneg_iff hf, ← E.ord_nonneg_iff (inv_ne_zero hf), E.ord_inv]
  omega

end GlobalTheory.FieldPair.Place
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorTwoByTwoTriangularProductStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_two_by_two_triangular_product : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (K : Type) [Field K] (S T C : Mat m K), Par m ⊤ S → Par m ⊤ T → AlmostLow τ a b C → AlmostLow τ a b (S * C * T) ∧ (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → (S * C * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * C x.1 x.2 x.2 * T x.1 x.2 x.2) ∧ (S * C * T) τ a b = S τ a a * C τ a b * T τ b b ∧ minor τ a b (S * C * T) = S τ a a * S τ b b * minor τ a b C * (T τ a a * T τ b b) := by
  first | exact @GlobalTheory.FlagPush.almostLow_mul_entries | exact GlobalTheory.FlagPush.almostLow_mul_entries | (intros; apply GlobalTheory.FlagPush.almostLow_mul_entries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyBoundedDenominators
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minpoly_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∃ D : ℕ, 0 < D ∧ ∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → ∀ k : ℕ, ∃ m : ℕ, IsIntegral ℤ ((p : G.F) ^ m * D * (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k) := by
  first | (exact @GlobalTheory.FinPtsAway.exists_den_minpoly_coeff) | (exact GlobalTheory.FinPtsAway.exists_den_minpoly_coeff) | (intros; apply GlobalTheory.FinPtsAway.exists_den_minpoly_coeff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyPadicBounded
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minpoly_padic_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ β : G.Cˣ, ∃ B : ℝ, ∀ (y : grp G β) (h : Gr G 1), f' (h⁻¹ * toP1 G β y * h) ≠ 0 → ∀ (φ : G.F →+* PadicAlgCl p) (k : ℕ), ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  first | (exact @GlobalTheory.LKCx.PadicPolys.minpoly_coeff_bdd) | (exact GlobalTheory.LKCx.PadicPolys.minpoly_coeff_bdd) | (intros; apply GlobalTheory.LKCx.PadicPolys.minpoly_coeff_bdd  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFiniteFrameLatticeFormsStatement
section
open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_finite_frameLatticeForms : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)) := by
  first | exact @GlobalTheory.ExpFrame.Frame.finite_latticeForms | exact GlobalTheory.ExpFrame.Frame.finite_latticeForms | (intros; apply GlobalTheory.ExpFrame.Frame.finite_latticeForms <;> assumption)
end

