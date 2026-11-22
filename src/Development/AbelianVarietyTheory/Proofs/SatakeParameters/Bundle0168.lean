import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeGLChartOfUnitaryGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitPrimeChart

theorem entries_of_stab {R K : Type} [CommRing R] [CommRing K] {n : ℕ} {Λ : (Fin n → R) → Prop} {O : R → Prop}
    {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R) (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1)
    (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {A B C : Matrix (Fin n) (Fin n) R}
    (h1 : ∀ z : Fin n → R, (∀ i, O (z i)) → Λ (ε • B *ᵥ z))
    (h2 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • y = ε • B *ᵥ z)
    (hA : ∀ y, Λ y → Λ (A *ᵥ y)) (hCB : C.map φ * B.map φ = 1) :
    ∀ i j, (C.map φ * A.map φ * B.map φ) i j ∈ OK := by
  intro i j
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have sm : ∀ x : Fin n → R, φ ∘ (ε • x) = φ ∘ x := fun x => funext fun i => by simp [hε]
  let z : Fin n → R := fun k => s ((Pi.single j (1 : K) : Fin n → K) k)
  have hz : ∀ k, O (z k) := fun k => hO' _ (by
    by_cases hk : k = j
    · subst hk; simp [one_mem]
    · simp [hk, zero_mem])
  have hz' : φ ∘ z = Pi.single j 1 := funext fun k => hs _
  obtain ⟨z', hz1, hz2⟩ := h2 _ (hA _ (h1 z hz))
  have e1 : A.map φ *ᵥ (B.map φ *ᵥ Pi.single j 1) = B.map φ *ᵥ (φ ∘ z') := by
    have := congrArg (φ ∘ ·) hz2
    simp only [sm] at this
    rw [mv, sm, mv, hz', mv] at this
    exact this
  have e2 : (C.map φ * A.map φ * B.map φ) i j = (φ ∘ z') i := by
    have : (C.map φ * A.map φ * B.map φ) *ᵥ Pi.single j 1 = φ ∘ z' := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec]
    have := congrFun this i
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  rw [e2]
  exact hO _ (hz1 i)

theorem conj_mul_eq_one {K : Type} [CommRing K] {n : ℕ} {X Y Z W : Matrix (Fin n) (Fin n) K} (h1 : Y * X = 1)
    (h2 : X * Y = 1) (h3 : Z * W = 1) : X * Z * Y * (X * W * Y) = 1 := by
  calc X * Z * Y * (X * W * Y) = X * (Z * ((Y * X) * (W * Y))) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.one_mul, ← Matrix.mul_assoc Z, h3, Matrix.one_mul, h2]

theorem conj_conj {K : Type} [CommRing K] {n : ℕ} {X Y Z : Matrix (Fin n) (Fin n) K} (h1 : Y * X = 1) :
    Y * (X * Z * Y) * X = Z := by
  calc Y * (X * Z * Y) * X = (Y * X) * Z * (Y * X) := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [h1, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.SplitPrimeChart

namespace GlobalTheory.SplitPrimeChart

open Formalism.L2.NTheta

set_option maxHeartbeats 1000000 in

theorem exists_chart : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ ρ : GA D V →* GL (Fin V.rank) (P.adicCompletion D.host.E), (∀ M : GL (Fin V.rank) (P.adicCompletion D.host.E), ∃ g, Formalism.L2.Theta.SuppAt e V g ∧ ρ g = M) ∧ (∀ k ∈ KsphC V ∅, ρ k ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P)) ∧ ∀ (g : GA D V) (a : Fin V.rank → ℤ), ∀ k₁ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ∀ k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) = (k₁ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) * Formalism.UG.diagPow D.host.E P (algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E)) a * (k₂ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) → DivAt V e (ϖ : D.host.E) (List.ofFn a) g := by
  intro D V P e he ϖ h1 h2
  have hee' : e * e = e := he.1.1
  have ht := GlobalTheory.SphLabelOps.tie_of_isPrimeIdem (P := P) (f := e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨φ, s, hs, hε, hφ, hO, hO', hinc⟩ := GlobalTheory.SphLabelOps.exists_component hee' ht
  obtain ⟨B, b1, b2⟩ := GlobalTheory.SphLabelOps.exists_basis V hee' ht
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, hee']
  obtain ⟨C, c1, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      finPart D e • (X * Y) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) → X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
      one_mul] at this
  let b : GL (Fin V.rank) (P.adicCompletion D.host.E) := ⟨B.map φ, C.map φ, mp _ _ c1, mp _ _ c2⟩
  let ρ : GA D V →* GL (Fin V.rank) (P.adicCompletion D.host.E) :=
    (MulAut.conj b⁻¹).toMonoidHom.comp ((Formalism.UG.bc φ).comp (finHom V))
  have hρ : ∀ g, ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) =
      C.map φ * (finMat D.sp.cm.sig V.gram g).map φ * B.map φ := fun g => by
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Units.val_mul]
    rfl
  refine ⟨ρ, fun M => ?_, fun k hk => ?_, fun g a k₁ hk₁ k₂ hk₂ hg => ?_⟩
  · have hsM : ∀ N : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E), (N.map s).map φ = N :=
      fun N => Matrix.ext fun i j => hs _
    have hm : finPart D e • ((B * (M : Matrix _ _ _).map s * C) * (B * ((M⁻¹ : GL _ _) : Matrix _ _ _).map s * C)) =
        finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      apply hφ
      have : ((B * (M : Matrix _ _ _).map s * C) * (B * ((M⁻¹ : GL _ _) : Matrix _ _ _).map s * C)).map φ =
          (1 : Matrix (Fin V.rank) (Fin V.rank) _).map φ := by
        simp only [Matrix.map_mul]
        rw [Matrix.map_one φ (map_zero φ) (map_one φ), hsM, hsM]
        exact conj_mul_eq_one (mp _ _ c2) (mp _ _ c1) (Units.mul_inv M)
      exact congrFun (congrFun this i) j
    obtain ⟨g, hgs, hg⟩ := GlobalTheory.SplitLift.split_lift V e he.1 _ _ hm
    refine ⟨g, hgs, Units.ext ?_⟩
    have hgm : (finMat D.sp.cm.sig V.gram g).map φ = (B * (M : Matrix _ _ _).map s * C).map φ :=
      Matrix.ext fun i j => by
        have := congrArg φ (congrFun (congrFun hg i) j)
        rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
          one_mul] at this
    rw [hρ, hgm, Matrix.map_mul, Matrix.map_mul, hsM]
    exact conj_conj (mp _ _ c2)
  · have hint : ∀ g ∈ KsphC V ∅, ∀ i j,
        ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) i j ∈
          Formalism.UG.Ov D.host.E P := by
      intro g hg i j
      rw [hρ]
      exact entries_of_stab (Λ := fun y => y ∈ LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b1
        (fun y hy => b2 y hy) (fun y hy => (hg.2.1 y).1 hy) (mp _ _ c2) i j
    have hk' : k⁻¹ ∈ KsphC V ∅ :=
      (GlobalTheory.SphLabelOps.mem_stabG _).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG k).2 hk))
    refine Formalism.UG.P.cartan_mem_of_entries _ _ (hint k hk) ?_
    rw [← map_inv]
    exact hint _ hk'
  · rw [GlobalTheory.DivDual.divAt_iff]
    refine ⟨List.length_ofFn, GlobalTheory.SphLabelOps.dv_of_cartan φ s hs hε hφ hO hO' (B := B) b1 b2
      (Formalism.UG.P.cartan_entries_of_mem _ _ hk₁) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₁))
      (Formalism.UG.P.cartan_entries_of_mem _ _ hk₂) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₂)) ?_⟩
    have e1 : (Matrix.diagonal fun i : Fin V.rank =>
        φ (finPart D (incA D ((ϖ : D.host.E) ^ ((List.ofFn a).getD i.1 0))))) =
        Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) a := by
      unfold Formalism.UG.diagPow
      congr 1
      funext i
      rw [hinc, map_zpow₀]
      simp
    rw [e1, ← hg, hρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mp _ _ c1, Matrix.one_mul]

end GlobalTheory.SplitPrimeChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvector
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

namespace GlobalTheory.TorusEigenform

section General

variable {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] [AddCommGroup V] [Module ℂ V]

theorem exists_char_of_isIrreducible {σ : Representation ℂ G V} (hs : IsSmooth σ) (hi : σ.IsIrreducible) :
    ∃ μ : G →* ℂˣ, ∀ g w, σ g w = (μ g : ℂ) • w := by
  have := nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h : ∀ g, ∃ c : ℂ, ∀ w, σ g w = c • w := fun g =>
    LocGL.exists_eq_smul_of_isSmooth hs hi
      ⟨σ g, fun a => by rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, mul_comm]⟩
  choose c hc using h
  let m : G →* ℂ :=
    { toFun := c
      map_one' := smul_left_injective ℂ hv (by simp [← hc])
      map_mul' := fun a b => smul_left_injective ℂ hv (by
        show c (a * b) • v = (c a * c b) • v
        rw [← hc, map_mul, Module.End.mul_apply, hc b, hc a, smul_smul]) }
  exact ⟨m.toHomUnits, fun g w => hc g w⟩

theorem exists_eigenform {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {χ : G →* ℂˣ} (hχ : IsSmoothChar χ) {x : V} (hx : x ≠ 0)
    (hxH : ∀ t ∈ H, ρ t x = (χ t : ℂ) • x) :
    ∃ (μ : G →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ g v, l (ρ g v) = (μ g : ℂ) * l v) ∧ ∀ h ∈ H, μ h = χ h := by
  let ρ' := twist ρ χ⁻¹
  have hρ' : ∀ g v, ρ' g v = ((χ g)⁻¹ : ℂˣ) • ρ g v := fun _ _ => rfl
  have hc := LocGL.isCompl_fixed_twKer (isSmooth_twist hρ hχ.inv) hH
  let T : Subrepresentation ρ := ⟨twKer ρ' H 1, fun g v hv => by
    have h1 : ρ' g v ∈ twKer ρ' H 1 :=
      twKer_le_comap ρ' H g (by rw [Subgroup.normalizer_eq_top]; trivial) hv
    have h2 := (twKer ρ' H 1).smul_mem (χ g : ℂ) h1
    rwa [hρ', ← Units.smul_def, smul_inv_smul] at h2⟩
  have hT : T ≠ ⊤ := fun h => by
    have h1 : x ∈ T.toSubmodule := by rw [h]; trivial
    have h2 : x ∈ fixed ρ' H := fun t => by
      rw [hρ', hxH t t.2, ← Units.smul_def, inv_smul_smul]; simp
    exact hx ((Submodule.disjoint_def.1 hc.disjoint) x h2 h1)
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨M, hM, hTM⟩ := (eq_top_or_exists_le_coatom T).resolve_left hT
  have hi := isIrreducible_subQuot hM.covBy_top
  let p : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap (subQuot ⊤ M) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hs : IsSmooth (subQuot ⊤ M) :=
    IsSubquotient.isSmooth ⟨⊤, p, Submodule.Quotient.mk_surjective _⟩ hρ
  obtain ⟨μ, hμ⟩ := exists_char_of_isIrreducible hs hi
  have hμM : ∀ g v, ρ g v - (μ g : ℂ) • v ∈ M.toSubmodule := fun g v => by
    have := hμ g (Submodule.Quotient.mk ⟨v, trivial⟩)
    exact (Submodule.Quotient.eq (M.toSubmodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype)
      (x := ⟨ρ g v, trivial⟩) (y := ⟨(μ g : ℂ) • v, trivial⟩)).1 this
  have hM' : M.toSubmodule < ⊤ := lt_top_iff_ne_top.2 fun h =>
    hM.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨l, hl0, hlM⟩ := Submodule.exists_le_ker_of_lt_top _ hM'
  have hle : ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := fun g v => by
    have := hlM (hμM g v)
    rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  refine ⟨μ, l, hl0, hle, fun h hh => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hl0 (LinearMap.ext hn)
  have h1 : ρ' h v - v ∈ T.toSubmodule := Submodule.subset_span ⟨⟨h, hh⟩, v, by simp⟩
  have h2 := hlM (hTM h1)
  rw [LinearMap.mem_ker, map_sub, hρ', Units.smul_def, map_smul, hle, sub_eq_zero, smul_eq_mul,
    ← mul_assoc] at h2
  have h3 := mul_right_cancel₀ hv (h2.trans (one_mul _).symm)
  rw [← Units.val_mul, Units.val_eq_one, inv_mul_eq_one] at h3
  exact h3.symm

end General

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem secondCountableTopology_units : SecondCountableTopology kˣ := by
  have : SecondCountableTopology k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    letI : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    open scoped Valued in
    have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    infer_instance
  exact Units.isEmbedding_val₀.secondCountableTopology

variable {k} in

theorem isSmoothChar_torusChar {n : ℕ} {θ : Fin n → kˣ →* ℂˣ} (hθ : ∀ i, IsSmoothChar (θ i)) :
    IsSmoothChar (torusChar θ) :=
  Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) (by
    show IsOpen _
    rw [MonoidHom.ker_one]
    exact isOpen_univ) fun i _ => (hθ i).comp _ (continuous_apply i)

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Fin n → kˣ) V) (x : V) (θ : Fin n → kˣ →* ℂˣ), IsSmooth ρ → HasFiniteLength ρ → (∀ i, IsSmoothChar (θ i)) → x ≠ 0 → (∀ t ∈ torusO k (Fin n), ρ t x = (torusChar θ t : ℂ) • x) → ∃ (ψ : Fin n → kˣ →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ t y, l (ρ t y) = (torusChar ψ t : ℂ) * l y) ∧ ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u := by
  intro k _ _ _ _ n V _ _ ρ x θ hρ hl hθ hx hxH
  haveI := secondCountableTopology_units k
  obtain ⟨μ, l, hl0, hle, hμ⟩ := exists_eigenform hρ hl (SmGL.UnramFixed.isCompact_torusO k (Fin n))
    (isSmoothChar_torusChar hθ) hx hxH
  refine ⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i), l, hl0, fun t y => ?_, fun i u hu => ?_⟩
  · rw [hle, torusChar_apply]
    conv_lhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  · have h := hμ (Pi.mulSingle i u) fun j => by
      by_cases h : j = i
      · subst h; simpa using hu
      · simp [Pi.mulSingle_eq_of_ne h]
    rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp), Pi.mulSingle_eq_same] at h
    exact h

end GlobalTheory.TorusEigenform
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryElementaryDivisorsInertPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertExist

section Local

open GlobalTheory.SelfDualGenus GlobalTheory.PlaceComp GlobalTheory.HeckeLabels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem mem_stdLat_iff {n : ℕ} (x : Fin n → E) :
    x ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) ↔ ∀ i, IsIntegral ℤ (x i) := by
  show x ∈ Formalism.L2.Col.stdLat E n ↔ _
  simp only [Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨x i, h⟩, rfl⟩⟩

theorem antiJ_herm (n : ℕ) (a b : Fin n) :
    ReciprocityTheory.ChartRestriction.G.FD.cc (Formalism.UG.antiJ E n a b) = Formalism.UG.antiJ E n b a := by
  simp only [Formalism.UG.antiJ, add_comm b.val a.val]
  split_ifs <;> simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_one, map_zero]

theorem antiJ_det_ne_zero (n : ℕ) : (Formalism.UG.antiJ E n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (GlobalTheory.DualDivU.antiJ_sq (L := E) (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem selfDual_antiJ (n : ℕ) (x : Fin n → E) :
    x ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) ↔
      ∀ y ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)),
        IsIntegral ℤ (ReciprocityTheory.ChartRestriction.G.FD.herm (Formalism.UG.antiJ E n) x y) := by
  rw [mem_stdLat_iff]
  constructor
  · intro hx y hy
    rw [mem_stdLat_iff] at hy
    refine IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ => ?_
    refine ((hx a).mul ?_).mul ?_
    · unfold Formalism.UG.antiJ; split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · exact (hy b).map (IsCMField.complexConj E : E →+* E).toIntAlgHom
  · intro h i
    have hy : (Pi.single i.rev (1 : E) : Fin n → E) ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) := by
      rw [mem_stdLat_iff]
      intro j
      by_cases hj : j = i.rev
      · subst hj; simpa using isIntegral_one
      · simpa [hj] using isIntegral_zero
    have := h _ hy
    convert this using 1
    simp [ReciprocityTheory.ChartRestriction.G.FD.herm, Formalism.UG.antiJ, Pi.single_apply, ReciprocityTheory.ChartRestriction.G.FD.cc]
    rw [Finset.sum_eq_single i]
    · rw [if_pos (by have := i.2; omega)]
    · intro b _ hb
      rw [if_neg]
      intro hc; apply hb; ext; have := i.2; have := b.2; omega
    · intro h; exact absurd (Finset.mem_univ i) h

theorem locLattice_le {n : ℕ} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    {x : Fin n → LocAlg v} (hx : x ∈ locLattice v (Formalism.L2.Col.stdLat E n)) (i : Fin n) : x i ∈ locOrder v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = y i := ⟨⟨y i, (mem_stdLat_iff y).1 hy i⟩, rfl⟩
    show locEmb v (y i) ∈ locOrder v
    rw [← hz]
    exact locEmb_mem_locOrder v z
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Subalgebra.smul_mem _ hx c

theorem mulVec_int {R : Type} [CommRing R] {O : Subring R} {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ i j, M i j ∈ O) {z : Fin n → R} (hz : ∀ i, z i ∈ O) (i : Fin n) : (M *ᵥ z) i ∈ O := by
  show ∑ j, M i j * z j ∈ O
  exact O.sum_mem fun j _ => mul_mem (hM i j) (hz j)

theorem single_int {R : Type} [CommRing R] {O : Subring R} {n : ℕ} (j i : Fin n) :
    (Pi.single j (1 : R) : Fin n → R) i ∈ O := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem exists_antiFrame [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (hc : CMData (maximalRealSubfield E) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (n : ℕ) :
    ∃ h : GL (Fin n) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E),
      Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) h.1 *
        (Formalism.UG.antiJ E n).map (inclR (Fv (maximalRealSubfield E) v)) * h.1 = 1 ∧
      (∀ i j, h.1 i j ∈ ordAt E v) ∧ ∀ i j, (h⁻¹).1 i j ∈ ordAt E v := by
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame (antiJ_herm n) (antiJ_det_ne_zero n)
    ⟨Formalism.L2.Col.stdLat_lattice.fg, Formalism.L2.Col.stdLat_lattice.span_eq_top⟩ (selfDual_antiJ n) v
  have hs : ∀ j, (Pi.single j (1 : LocAlg v) : Fin n → LocAlg v) ∈ locLattice v (Formalism.L2.Col.stdLat E n) := by
    intro j
    refine Submodule.subset_span ⟨Pi.single j 1, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← SetLike.mem_coe, mem_stdLat_iff]
      intro i
      by_cases hi : i = j
      · subst hi; simpa using isIntegral_one
      · simpa [hi] using isIntegral_zero
    · funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
  refine ⟨h, ?_, fun i j => ?_, fun i j => ?_⟩
  · have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
      Matrix.transpose_one] at h3
    have hT : ((Formalism.UG.antiJ E n).map (locEmb v))ᵀ = (Formalism.UG.antiJ E n).map (locEmb v) := by
      ext a b; simp only [Matrix.transpose_apply, Matrix.map_apply, Formalism.UG.antiJ, add_comm b.val a.val]
    rw [hT] at h3
    exact h3
  · rw [mem_ordAt_iff]
    have hm : (fun k => (h.1 *ᵥ Pi.single j 1) k) ∈ locLattice v (Formalism.L2.Col.stdLat E n) := by
      rw [h2]
      intro k
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact single_int (O := (locOrder v).toSubring) j k
    have := locLattice_le v hm i
    rw [Matrix.mulVec_single_one] at this
    exact this
  · rw [mem_ordAt_iff]
    have := (h2 _).1 (hs j) i
    rw [Matrix.mulVec_single_one] at this
    exact this

theorem exists_std [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (hc : CMData (maximalRealSubfield E) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (n : ℕ) {ϖ : E} (h0 : ϖ ≠ 0) (hσ : hc.sig ϖ = ϖ) (d : ℕ → ℤ) (hd : ∀ i : Fin n, d i.rev.1 = -d i.1) :
    ∃ u ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig) (1 : Matrix (Fin n) (Fin n) _),
      StdDiv (ordAt E v) 1 (fun i : Fin n => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)) u.1 := by
  obtain ⟨h, hh, hi, hi'⟩ := exists_antiFrame hc v n
  have hσι : ∀ x : E, sigR (Fv (maximalRealSubfield E) v) hc.sig (inclR (Fv (maximalRealSubfield E) v) x) =
      inclR (Fv (maximalRealSubfield E) v) (hc.sig x) := fun x => by
    show (Algebra.TensorProduct.map (AlgHom.id _ _) hc.sig) ((1 : Fv (maximalRealSubfield E) v) ⊗ₜ x) =
      (1 : Fv (maximalRealSubfield E) v) ⊗ₜ hc.sig x
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  let t : Fin n → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E :=
    fun i => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)
  let t' : Fin n → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E :=
    fun i => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ (-d i.1))
  have tt : ∀ i, t i * t' i = 1 := fun i => by
    simp only [t, t', ← map_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, map_one]
  let T : GL (Fin n) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) :=
    ⟨Matrix.diagonal t, Matrix.diagonal t',
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact tt i,
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [mul_comm]; exact tt i⟩
  have hT : T ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig)
      ((Formalism.UG.antiJ E n).map (inclR (Fv (maximalRealSubfield E) v))) := by
    show Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) (Matrix.diagonal t) * _ * Matrix.diagonal t = _
    rw [Formalism.UG.cT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
    by_cases hij : i.val + j.val + 1 = n
    · have hj : j = i.rev := Fin.ext (by rw [Fin.val_rev]; omega)
      subst hj
      simp only [Formalism.UG.antiJ, if_pos hij, map_one, mul_one]
      show sigR (Fv (maximalRealSubfield E) v) hc.sig (inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)) *
        inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.rev.1) = 1
      rw [hσι, map_zpow₀, hσ, hd, ← map_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, map_one]
    · simp only [Formalism.UG.antiJ, if_neg hij, map_zero, mul_zero, zero_mul]
  have hu := conj_mem_UJ _ hh hT
  have hTv : ∀ w, T.1 *ᵥ w = t * w := fun w => funext fun k => by
    show (Matrix.diagonal t *ᵥ w) k = t k * w k
    rw [Matrix.mulVec_diagonal]
  refine ⟨h⁻¹ * T * h, hu, (h⁻¹).1, fun z hz i => ?_, fun y hy => ⟨h.1 *ᵥ y, mulVec_int hi hy, ?_⟩,
    fun y hy => ⟨h.1 *ᵥ y, mulVec_int hi hy, ?_⟩, fun z hz => ⟨(h⁻¹).1 *ᵥ z, mulVec_int hi' hz, ?_⟩⟩
  · rw [one_smul]; exact mulVec_int hi' hz i
  · rw [one_smul, one_smul, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · rw [one_smul, one_smul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTv]
  · have hz' : h.1 *ᵥ ((h⁻¹).1 *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [one_smul, one_smul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz', hTv]

end Local

section Host

open GlobalTheory.PlaceComp

theorem exists_suppF_divAt : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (x : 𝓞 D.host.F) (ϖ : 𝓞 D.host.E) (d : List ℤ), IsPrimeIdem P e e → (ϖ : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → dualLab d = d → ∃ g : GA D V, SuppF V e g ∧ DivAt V e (ϖ : D.host.E) d g := by
  intro D V P e x ϖ d hP hx h1 h2 hlen hdual
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  obtain ⟨v, hf, hef⟩ : ∃ v, GlobalTheory.PlaceComp.IsIdemOf D.host.E v e ∧ e * e = e := by
    rcases id hP with ⟨⟨⟨a1, a2, v, ε, ⟨a, rfl, b1, b2⟩, a3⟩, -⟩, he⟩ | ⟨-, ⟨v, ε, ⟨a, rfl, b1, b2⟩, a3⟩, -⟩
    · rw [← he] at a3
      exact ⟨v, a3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap b1 b2, ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e hP).1⟩
    · exact ⟨v, a3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap b1 b2, ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e hP).1⟩
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]
    exact zero_mem _)
  have hσ : D.sp.cm.sig (ϖ : D.host.E) = ϖ := by
    rw [hx]
    exact D.sp.cm.sig.commutes _
  have hd : ∀ i : Fin V.rank, d.getD i.rev.1 0 = -d.getD i.1 0 := fun i => by
    have := GlobalTheory.DualDivU.getD_dualLab d hlen i
    rw [hdual] at this
    rw [this, neg_neg]
  obtain ⟨u, hu, hs⟩ := GlobalTheory.InertExist.exists_std D.sp.cm v V.rank h0 hσ (fun i => d.getD i 0) hd
  obtain ⟨g, hg, hg'⟩ := (GlobalTheory.HeckeLabels.exists_div_iff (E := D.host.E) D.sp.cm V hf hef (ϖ : D.host.E)
    (fun i => d.getD i 0) rfl).2 ⟨u, hu, by rw [hf.2.1]; exact hs⟩
  exact ⟨g, hg, hlen, hg'⟩

end Host

end GlobalTheory.InertExist
end
end

