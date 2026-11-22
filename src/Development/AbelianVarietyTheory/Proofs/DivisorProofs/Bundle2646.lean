import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatchingExists
section
noncomputable section

namespace GlobalTheory.ThK.Partner

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.BigNZ
open scoped TensorProduct Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Pair

variable {n d : ℕ} {X : Spc F E n} {Y : Spc F E d}

theorem pure_smul (c : ℂ) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) :
    pure (c • f) φ = c • pure f φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem polData_sum {B : Base F E} {M : Model σ X Y} {Φ} (h : Φ ∈ PolData B M) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol B.ψ B.emb ∧ Fam M (φ i)) ∧ Φ = ∑ i, pure (f i) (φ i) := by
  obtain ⟨m, c, g, e⟩ := Submodule.mem_span_set'.1 h
  choose f hf φ hφ hv hΦ using fun i => (g i).2
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hv i⟩, ?_⟩
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pure_smul, ← hΦ i]

theorem finite_bad {M : Model σ X Y} {m : ℕ} {φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ}
    (h : ∀ i, Fam M (φ i)) : {v | ∃ i, φ i v ≠ M.vac v}.Finite := by
  have e : {v | ∃ i, φ i v ≠ M.vac v} = ⋃ i, {v | φ i v ≠ M.vac v} := by ext; simp
  rw [e]
  exact Set.finite_iUnion fun i => eventually_cofinite.1 (h i).2

end Pair

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem partner_of_big (hK : KP) (hM : IsMatched B G X om om' R Rf) {Φ} (hΦ : Φ ∈ PolData B G.M) :
    ∃ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' := by
  have hco : Coinv B G X om om' Rf := GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM
  obtain ⟨m, f, φ, hfφ, rfl⟩ := polData_sum hΦ
  have hfin := finite_bad fun i => (hfφ i).2
  let T : Finset (Pl F) := X.T ∪ {B.v₁} ∪ hfin.toFinset
  have hXT : X.T ⊆ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have h1 : B.v₁ ∈ T := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hout : ∀ i, ∀ v ∉ T, φ i v = G.M.vac v := fun i v hv => by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨i, hc⟩))
  have hre : ∀ i, ∃ g ∈ G.M'.Pol B.ψ B.emb, R.p' g = R.p (f i) := fun i =>
    Submodule.mem_map.1 (hM.real.quot'.onto ▸ Submodule.mem_top)
  choose f' hf' ef using hre
  have hsb : ∀ i v, ∃ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ = Rf.p v (φ i v) := fun i v =>
    Submodule.mem_map.1 ((hM.fin.onto' v).symm ▸ Submodule.mem_top)
  choose χ hχ eχ using hsb
  have hso : ∀ i, ∃ ζ ∈ G.M'.SoLoc B.ψ B.τ₁, Rf.p' B.v₁ ζ = Rf.p B.v₁ (φ i B.v₁) := fun i =>
    (hco.1 B.v₁ hM.triple.chars.good).2.2.1 B.τ₁ _
  choose ζ hζ eζ using hso
  let φ₀ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun i v => if v ∈ T then χ i v else G.M'.vac v
  let φ' : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun i => Function.update (φ₀ i) B.v₁ (ζ i)
  have fam₀ : ∀ i, Fam G.M' (φ₀ i) := fun i => by
    refine ⟨fun v => ?_, T.eventually_cofinite_notMem.mono fun v hv => if_neg hv⟩
    by_cases hv : v ∈ T
    · simp only [φ₀, if_pos hv]; exact hχ i v
    · simp only [φ₀, if_neg hv]; exact (hM.triple.geo.hM'.vac v).1
  have fam' : ∀ i, Fam G.M' (φ' i) := fun i => (fam₀ i).update B.v₁ (hζ i).1
  have out' : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := fun i v hv => by
    have hne : v ≠ B.v₁ := fun e => hv (e ▸ h1)
    simp only [φ', Function.update_of_ne hne, φ₀, if_neg hv]
  refine ⟨∑ i, pure (f' i) (φ' i), Submodule.sum_mem _ fun i _ => Submodule.subset_span
    ⟨f' i, φ' i, (fam' i).1, (fam' i).2, by simp only [φ', Function.update_self]; exact hζ i, rfl⟩, ?_⟩
  refine ⟨T, hXT, m, m, f, φ, f', φ', fun i => ⟨(hfφ i).1, (hfφ i).2.1, hout i⟩,
    fun i => ⟨hf' i, (fam' i).1, out' i⟩, rfl, rfl, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ef i]
  congr 2
  funext ⟨v, hvT⟩
  by_cases hv : v = B.v₁
  · subst hv
    simp only [φ', Function.update_self, eζ]
  · simp only [φ', Function.update_of_ne hv, φ₀, if_pos hvT, eχ]

theorem partner_of_small (hM : IsMatched B G X om om' R Rf) {Φ'} (hΦ' : Φ' ∈ PolData B G.M') :
    ∃ Φ, PolMatch B G X R Rf Φ Φ' := by
  obtain ⟨m, f', φ', hfφ, rfl⟩ := polData_sum hΦ'
  have hfin := finite_bad fun i => (hfφ i).2
  let T : Finset (Pl F) := X.T ∪ hfin.toFinset
  have hXT : X.T ⊆ T := Finset.subset_union_left
  have hout : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := fun i v hv => by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨i, hc⟩))
  have hre : ∀ i, ∃ g ∈ G.M.Pol B.ψ B.emb, R.p g = R.p' (f' i) := fun i =>
    Submodule.mem_map.1 (hM.real.quot.onto ▸ Submodule.mem_top)
  choose f hf ef using hre
  have hsb : ∀ i v, ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = Rf.p' v (φ' i v) := fun i v =>
    Submodule.mem_map.1 ((hM.fin.onto v).symm ▸ Submodule.mem_top)
  choose χ hχ eχ using hsb
  let φ : Fin m → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := fun i v => if v ∈ T then χ i v else G.M.vac v
  have hφ : ∀ i v, φ i v ∈ SB _ := fun i v => by
    by_cases hv : v ∈ T
    · simp only [φ, if_pos hv]; exact hχ i v
    · simp only [φ, if_neg hv]; exact (hM.triple.geo.hM.vac v).1
  refine ⟨∑ i, pure (f i) (φ i), T, hXT, m, m, f, φ, f', φ', fun i => ⟨hf i, hφ i, fun v hv => if_neg hv⟩,
    fun i => ⟨(hfφ i).1, (hfφ i).2.1, hout i⟩, rfl, rfl, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ef i]
  congr 2
  funext ⟨v, hvT⟩
  simp only [φ, if_pos hvT, eχ]

theorem match_of_polMatch (hM : IsMatched B G X om om' R Rf) {Φ Φ'} (hS : Φ' ∈ G.M'.So B.ψ B.τ₁)
    (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' ∧ Match B G X R Rf Φ Φ' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hi, hj, e1, e2, -⟩ := id h
  have fam : ∀ i, Fam G.M (φ i) := fun i => ⟨(hi i).2.1, T.eventually_cofinite_notMem.mono (hi i).2.2⟩
  have fam' : ∀ j, Fam G.M' (φ' j) := fun j => ⟨(hj j).2.1, T.eventually_cofinite_notMem.mono (hj j).2.2⟩
  refine ⟨e1 ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hi i).1, φ i, (fam i).1, (fam i).2, rfl⟩,
    e2 ▸ Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, (hj j).1, φ' j, (fam' j).1, (fam' j).2, rfl⟩,
    hS, m, m', fun i => finPartFn (φ i), f, fun _ => f, fun j => finPartFn (φ' j), f', fun _ => f',
    fun i => ⟨(fam i).sb hM.triple.geo.hM, tendsto_const_nhds⟩, fun j => ⟨(fam' j).sb hM.triple.geo.hM', tendsto_const_nhds⟩,
    e1, e2, fun _ => ⟨?_, ?_⟩⟩
  · show ∑ j, pure (f' j) (φ' j) ∈ _
    rw [← e2]; exact hS
  · show PolMatch B G X R Rf (∑ i, pure (f i) (φ i)) (∑ j, pure (f' j) (φ' j))
    rw [← e1, ← e2]; exact h

end GlobalTheory.ThK.Partner

namespace GlobalTheory.ThK

theorem matchEx_of_classicalTheorems (hK : KP) : MatchEx := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  exact ⟨fun Φ hΦ => Partner.partner_of_big hK hM hΦ, fun Φ' hΦ' => Partner.partner_of_small hM hΦ',
    fun Φ Φ' hS h => Partner.match_of_polMatch hM hS h⟩

end GlobalTheory.ThK

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSquareFactorizationSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.SquareSpread

theorem germ_res_hom {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) {x : X} (hx : x ∈ V) (s : Γ(X, U)) :
    (X.presheaf.germ V x hx).hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (X.presheaf.germ U x (h hx)).hom s :=
  TopCat.Presheaf.germ_res_apply _ (homOfLE h) x hx s

theorem res_res_hom {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_res_eq {X : Scheme.{0}} {U : X.Opens} {x : X} (hx : x ∈ U) (s t : Γ(X, U))
    (h : (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom t) :
    ∃ W : X.Opens, ∃ hW : W ≤ U, x ∈ W ∧
      (X.presheaf.map (homOfLE hW).op).hom s = (X.presheaf.map (homOfLE hW).op).hom t := by
  obtain ⟨W, hxW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq X.presheaf x hx hx s t h
  refine ⟨W, iU.le, hxW, ?_⟩
  have h1 : iU = homOfLE iU.le := rfl
  have h2 : iV = homOfLE iU.le := Subsingleton.elim _ _
  rw [h1] at e
  rw [h2] at e
  exact e

end GlobalTheory.Mum.SquareSpread

open GlobalTheory.Mum.SquareSpread in

theorem GlobalTheory.Mum.unit_mul_sq_spread : ∀ (X : Scheme.{0}) (L2 : LB X) (h : L2.Sec) (x : X) (j₀ : L2.ι) (hx : x ∈ L2.U j₀) (u : (X.presheaf.stalk x)ˣ) (a : X.presheaf.stalk x), a ≠ 0 → (X.presheaf.germ (L2.U j₀) x hx).hom (h.f j₀) = u * a ^ 2 → ∃ V : X.Opens, x ∈ V ∧ ∃ a : Γ(X, V), a ≠ 0 ∧ ∀ j, ∃ u : Γ(X, V ⊓ L2.U j)ˣ, (X.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(X, V ⊓ L2.U j)) * (X.presheaf.map (homOfLE inf_le_left).op).hom a ^ 2 := by
  intro X L2 h x j₀ hx u a ha hh

  obtain ⟨W₁, hW₁, hx₁, a', ha'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf a hx
  obtain ⟨W₂, hW₂, hx₂, u', hu'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf (u : X.presheaf.stalk x) hx₁
  obtain ⟨W₃, hW₃, hx₃, v', hv'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) hx₂
  have l31 : W₃ ≤ W₁ := hW₃.trans hW₂
  have l30 : W₃ ≤ L2.U j₀ := l31.trans hW₁
  set A : Γ(X, W₃) := (X.presheaf.map (homOfLE l31).op).hom a' with hA
  set U' : Γ(X, W₃) := (X.presheaf.map (homOfLE hW₃).op).hom u' with hU'
  set H : Γ(X, W₃) := (X.presheaf.map (homOfLE l30).op).hom (h.f j₀) with hH
  have gA : (X.presheaf.germ W₃ x hx₃).hom A = a := by rw [hA, germ_res_hom]; exact ha'
  have gU : (X.presheaf.germ W₃ x hx₃).hom U' = u := by rw [hU', germ_res_hom]; exact hu'
  have gV : (X.presheaf.germ W₃ x hx₃).hom v' = ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) := hv'
  have gH : (X.presheaf.germ W₃ x hx₃).hom H = u * a ^ 2 := by rw [hH, germ_res_hom]; exact hh
  obtain ⟨W₄, hW₄, hx₄, e₄⟩ := exists_res_eq hx₃ (U' * v') 1 (by
    rw [map_mul, map_one, gU, gV, Units.mul_inv])
  obtain ⟨W₅, hW₅, hx₅, e₅⟩ := exists_res_eq hx₃ H (U' * A ^ 2) (by
    rw [map_mul, map_pow, gU, gA, gH])

  have lV3 : W₄ ⊓ W₅ ≤ W₃ := inf_le_left.trans hW₄
  have hxV : x ∈ W₄ ⊓ W₅ := ⟨hx₄, hx₅⟩
  have e₄' : (X.presheaf.map (homOfLE lV3).op).hom U' * (X.presheaf.map (homOfLE lV3).op).hom v' = 1 := by
    rw [← map_mul, ← map_one (X.presheaf.map (homOfLE lV3).op).hom, ← res_res_hom hW₄ (inf_le_left : W₄ ⊓ W₅ ≤ W₄),
      ← res_res_hom hW₄ (inf_le_left : W₄ ⊓ W₅ ≤ W₄) 1, e₄]
  have e₅' : (X.presheaf.map (homOfLE lV3).op).hom H = (X.presheaf.map (homOfLE lV3).op).hom U' *
      ((X.presheaf.map (homOfLE lV3).op).hom A) ^ 2 := by
    rw [← map_pow, ← map_mul, ← res_res_hom hW₅ (inf_le_right : W₄ ⊓ W₅ ≤ W₅),
      ← res_res_hom hW₅ (inf_le_right : W₄ ⊓ W₅ ≤ W₅) (U' * A ^ 2), e₅]
  let uV : Γ(X, W₄ ⊓ W₅)ˣ := ⟨_, _, e₄', by rw [mul_comm]; exact e₄'⟩
  refine ⟨W₄ ⊓ W₅, hxV, (X.presheaf.map (homOfLE lV3).op).hom A, ?_, ?_⟩
  · intro h0
    apply ha
    rw [← gA, ← germ_res_hom lV3 hxV, h0, map_zero]
  · intro j
    have k : W₄ ⊓ W₅ ⊓ L2.U j ≤ L2.U j ⊓ L2.U j₀ := le_inf inf_le_right (inf_le_left.trans (lV3.trans l30))
    refine ⟨res k (L2.g j j₀) * Units.map (X.presheaf.map (homOfLE (inf_le_left : W₄ ⊓ W₅ ⊓ L2.U j ≤ W₄ ⊓ W₅)).op).hom uV, ?_⟩
    have c := congrArg (X.presheaf.map (homOfLE k).op).hom (h.compat j j₀)
    rw [map_mul, res_res_hom, res_res_hom] at c
    have e6 := congrArg (X.presheaf.map (homOfLE (inf_le_left : W₄ ⊓ W₅ ⊓ L2.U j ≤ W₄ ⊓ W₅)).op).hom e₅'
    rw [map_mul, map_pow, hH, res_res_hom, res_res_hom, res_res_hom] at e6
    rw [Units.val_mul, Units.coe_map, res, Units.coe_map]
    simp only [MonoidHom.coe_coe, hA, res_res_hom] at e6 ⊢
    rw [c, e6, _root_.mul_assoc]
    congr 2
    exact (res_res_hom lV3 _ U').symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationTensorPrimeComapCompat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open KaehlerDifferential TensorProduct in

theorem mapBaseChange_residueField_bijective_of_etale_fibre :
    ∀ (A C B Ω : Type) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] [Field Ω] [Algebra A Ω] (Q : Ideal B) [Q.IsPrime] (Q' : Ideal (TensorProduct A Ω B)) [Q'.IsPrime] (f : TensorProduct A Ω B), Q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B) = Q → f ∉ Q' → ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom).Etale → Function.Bijective ((KaehlerDifferential.mapBaseChange A C B).lTensor Q.ResidueField) := by
  intro A C B Ω _ _ _ _ _ _ _ _ _ Q _ Q' _ f hQ hf het
  classical
  letI : Algebra C (TensorProduct A Ω C) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra B (TensorProduct A Ω B) := Algebra.TensorProduct.rightAlgebra
  set ψ := ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp
    (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom) with hψ
  letI : Algebra (TensorProduct A Ω C) (Localization.Away f) := ψ.toAlgebra
  haveI : Algebra.Etale (TensorProduct A Ω C) (Localization.Away f) := het
  haveI : IsScalarTower Ω (TensorProduct A Ω C) (Localization.Away f) :=
    IsScalarTower.of_algebraMap_eq fun w => by
      change _ = ψ _
      simp [hψ, Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply Ω (TensorProduct A Ω B) (Localization.Away f)]

  have hunit : IsUnit (algebraMap (TensorProduct A Ω B) Q'.ResidueField f) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]; exact hf
  letI : Algebra (Localization.Away f) Q'.ResidueField :=
    (Localization.awayLift (algebraMap (TensorProduct A Ω B) Q'.ResidueField) f hunit).toAlgebra
  have hlift : ∀ s, algebraMap (Localization.Away f) Q'.ResidueField
      (algebraMap (TensorProduct A Ω B) (Localization.Away f) s) =
      algebraMap (TensorProduct A Ω B) Q'.ResidueField s := fun s =>
    IsLocalization.Away.lift_eq f hunit s
  have hBK : ∀ b : B, algebraMap B Q'.ResidueField b =
      algebraMap (TensorProduct A Ω B) Q'.ResidueField (algebraMap B (TensorProduct A Ω B) b) := by
    intro b
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q') Q'.ResidueField,
      IsScalarTower.algebraMap_apply B (TensorProduct A Ω B) (Localization.AtPrime Q'),
      ← IsScalarTower.algebraMap_apply]
  letI : Algebra C Q'.ResidueField := ((algebraMap B Q'.ResidueField).comp (algebraMap C B)).toAlgebra
  haveI : IsScalarTower C B Q'.ResidueField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨eB, heB⟩ := GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale A Ω B (TensorProduct A Ω B)
    (Localization.Away f) Q'.ResidueField (fun x => by rw [hlift, hBK])
  obtain ⟨eC, heC⟩ := GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale A Ω C (TensorProduct A Ω C)
    (Localization.Away f) Q'.ResidueField (fun x => by
      change algebraMap B Q'.ResidueField (algebraMap C B x) =
        algebraMap (Localization.Away f) Q'.ResidueField (ψ ((1 : Ω) ⊗ₜ[A] x))
      rw [hBK, hψ, RingHom.comp_apply, hlift]
      congr 1)
  set K := Q'.ResidueField
  let E := eC.trans eB.symm
  have hE : ∀ c : C, E ((1 : K) ⊗ₜ[C] KaehlerDifferential.D A C c) =
      (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (algebraMap C B c) := by
    intro c
    simp only [E, LinearEquiv.trans_apply, heC, LinearEquiv.symm_apply_eq, heB]
    rfl
  have hE' : ∀ ω : Ω[C⁄A], E ((1 : K) ⊗ₜ[C] ω) =
      (1 : K) ⊗ₜ[B] KaehlerDifferential.map A A C B ω := by
    intro ω
    have hω : ω ∈ Submodule.span C (Set.range (KaehlerDifferential.D A C)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; rw [hE, KaehlerDifferential.map_D]
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add, TensorProduct.tmul_add]
    | smul c x _ hx =>
      have h1 : (1 : K) ⊗ₜ[C] (c • x) = algebraMap C K c • ((1 : K) ⊗ₜ[C] x) := by
        rw [TensorProduct.tmul_smul]; exact (algebraMap_smul K c _).symm
      rw [h1, map_smul, hx, LinearMap.map_smul_of_tower, ← algebraMap_smul B c,
        TensorProduct.tmul_smul, ← algebraMap_smul K (algebraMap C B c)]
      rfl
  have hE'' : ∀ (k : K) (ω : Ω[C⁄A]), E (k ⊗ₜ[C] ω) = k ⊗ₜ[B] KaehlerDifferential.map A A C B ω := by
    intro k ω
    have h1 : k ⊗ₜ[C] ω = k • ((1 : K) ⊗ₜ[C] ω) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h1, map_smul, hE', TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  letI : Algebra Q.ResidueField K :=
    (Ideal.ResidueField.map Q Q' (algebraMap B (TensorProduct A Ω B)) (by rw [← hQ]; rfl)).toAlgebra
  haveI : IsScalarTower B Q.ResidueField K := IsScalarTower.of_algebraMap_eq fun b => by
    rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap, hBK]
  rw [← LinearMap.baseChange_eq_ltensor,
    ← Module.FaithfullyFlat.lTensor_bijective_iff_bijective Q.ResidueField K]
  let cM := TensorProduct.AlgebraTensorModule.cancelBaseChange B Q.ResidueField K K
    (TensorProduct C B Ω[C⁄A])
  let cN := TensorProduct.AlgebraTensorModule.cancelBaseChange B Q.ResidueField K K Ω[B⁄A]
  let cC := TensorProduct.AlgebraTensorModule.cancelBaseChange C B K K Ω[C⁄A]
  have key : ∀ z, ((KaehlerDifferential.mapBaseChange A C B).baseChange Q.ResidueField).lTensor K z =
      cN.symm (E (cC (cM z))) := by
    intro z
    rw [LinearEquiv.eq_symm_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul k y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
      | tmul l m =>
        induction m using TensorProduct.induction_on with
        | zero => simp
        | add m₁ m₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
        | tmul b ω =>
          simp only [cM, cN, cC, LinearMap.lTensor_tmul, LinearMap.baseChange_tmul,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            KaehlerDifferential.mapBaseChange_tmul, hE'', TensorProduct.smul_tmul]
  have hfun : ⇑(((KaehlerDifferential.mapBaseChange A C B).baseChange Q.ResidueField).lTensor K) =
      ⇑cN.symm ∘ ⇑E ∘ ⇑cC ∘ ⇑cM := funext key
  rw [hfun]
  exact cN.symm.bijective.comp (E.bijective.comp (cC.bijective.comp cM.bijective))

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerDetEqConstMulHorizontal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogPole

theorem logDet_eq_hor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (s : ℚ), s ≠ 0 → KSCompare TF s → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (b : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), (∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (b j).1 (GlobalTheory.LogKSDiv.symPair e (ε j))) → ∀ (o : Fin Dw.dim ≃ HIx Dw (psiSet H)), ∃ a : ℚ, a ≠ 0 ∧ ∀ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1) (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), (∀ σ, (g σ).det = 1) → GlobalTheory.Frames.FrChg g 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (w : HIx Dw (psiSet H) → FrPt Xo c (DualNumber K)) (hw : ∀ b, ⊤ ≤ (frX (w b) ≫ TF.Y.j) ⁻¹ᵁ U.1), (∀ b, IsDef P (w b) ∧ FlagTan.IsKS (psiSet H) P (w b).x (Pi.single b 1)) → ev (frX P₀ ≫ TF.Y.j) U.1 hU (logDet (fun j => (b j).1) x) = (a : K) * (Matrix.of fun i j => (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd).det := by
  intro E _ _ _ H Dw l Xo c TF s hs hcmp hKS U n e v hv ε b hb o
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.balancedSymmetricPairMatrix_horizontal_single ε
  refine ⟨s ^ Dw.dim * ((Equiv.Perm.sign (κ.trans o.symm) : ℤ) : ℚ), ?_, ?_⟩
  · have : ((Equiv.Perm.sign (κ.trans o.symm) : ℤ) : ℚ) ≠ 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (κ.trans o.symm)) with h | h <;> simp [h]
    exact mul_ne_zero (pow_ne_zero _ hs) this
  intro x K _ _ P₀ P hU g hg hP hB w hw hwk
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.tangentDerivative_linear_in_kodairaSpencerMatrix_of_iso TF K P₀ (hKS K P₀) U.1 hU
  choose y' hy' hsnd hred hev using fun j => GlobalTheory.T.exists_dualNumberTangentPoint_of_logarithmicDerivation TF U (b j) K P₀ hU
  have hKSj : ∀ j, FlagTan.IsKS (psiSet H) P₀ (y' j ≫ pullback.fst _ _)
      (fun k => (s : K) * (Pi.single (κ j) (1 : K) : HIx Dw (psiSet H) → K) k) := by
    intro j
    have := hcmp U n e v hv (b j) _ (hb j) K P₀ hU hB (y' j) (hy' j) (hsnd j) (hev j)
    convert this using 3 with k
    rw [hκ (ev (frX P₀ ≫ TF.Y.j) U.1 hU) n e j k]
  have hL : ∀ i j, ev (frX P₀ ≫ TF.Y.j) U.1 hU ((b j).1 (x i)) = (s : K) * δ (κ j) (x i) := by
    intro i j
    have h1 := hδ (y' j) (hy' j) (hsnd j) (hred j) _ (hKSj j) (x i)
    rw [hev j] at h1
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h1
    rw [h1]
    simp [Pi.single_apply, mul_comm, mul_left_comm]
  have hx : P.x = P₀.x := hP.1
  have hR : ∀ i j, (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd =
      ∑ k, FlagTan.ksChg (psiSet H) g (Pi.single (o j) 1 : HIx Dw (psiSet H) → K) k * δ k (x i) := by
    intro i j
    have hk := (FlagTan.isKS_frChg_iff (psiSet H) g 1 P₀ P hP _ _).1 (hwk (o j)).2
    refine hδ (frX (w (o j))) (hw _) (GlobalTheory.FlagMod.frX_snd _) ?_ _ ?_ (x i)
    · rw [GlobalTheory.FlagMod.frX_frMap (hwk (o j)).1]
      exact GlobalTheory.FlagMod.eq_frX P₀ (by rw [GlobalTheory.FlagMod.frX_fst, hx]) (GlobalTheory.FlagMod.frX_snd P)
    · rw [GlobalTheory.FlagMod.frX_fst]; exact hk
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin Dw.dim) (Fin Dw.dim) K, A = Matrix.of fun i j => δ (o j) (x i) := ⟨_, rfl⟩
  have eL : (ev (frX P₀ ≫ TF.Y.j) U.1 hU).mapMatrix (Matrix.of fun i j => (b j).1 (x i)) =
      (s : K) • A.submatrix id (κ.trans o.symm) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hL, hA]
    simp
  have eR : (Matrix.of fun i j => (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd) =
      A * Matrix.of fun i j => FlagTan.ksChg (psiSet H) g (Pi.single (o j) 1 : HIx Dw (psiSet H) → K) (o i) := by
    ext i j
    rw [Matrix.of_apply, hR, Matrix.mul_apply, ← Equiv.sum_comp o, hA]
    simp only [Matrix.of_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [logDet, RingHom.map_det, eR, Matrix.det_mul, GlobalTheory.T.det_flagTangentConjugateMatrixChange_eq_one K g hg o, mul_one, eL, Matrix.det_smul,
    Matrix.det_permute', Fintype.card_fin]
  push_cast
  ring

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisSectionsSplitStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayer_vietoris_sections_split : ∀ (Y : Scheme.{0}) (F : Y.Modules) (W₁ W₂ : Y.Opens), Subsingleton (cohOn F (W₁ ⊔ W₂) 1) → ∀ t : sectionsOn F (W₁ ⊓ W₂), ∃ (a : sectionsOn F W₁) (b : sectionsOn F W₂), t = sectionsOn.res Γ(Y, ⊤) F inf_le_right b - sectionsOn.res Γ(Y, ⊤) F inf_le_left a := by
  first | exact @GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn | exact GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn | (intros; apply GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedPointsClosedFibreMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_of_closedPoints_closedFibre_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] (T : Scheme.{0}) (q : T ⟶ Sp R),
    LocallyOfFiniteType q → ∀ U : T.Opens, (∀ x : T, IsClosed ({x} : Set T) → q x = closedPoint R → x ∈ U) →
    ∀ x : T, q x = closedPoint R → x ∈ U := by
  intro R _ _ T q hq U hU x hx
  by_contra hxU
  set c : Sp R := closedPoint R
  have hc : IsClosed ({c} : Set (Sp R)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (IsLocalRing.maximalIdeal.isMaximal R)
  have hft : LocallyOfFiniteType (q.fiberToSpecResidueField c) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : JacobsonSpace (q.fiber c) := LocallyOfFiniteType.jacobsonSpace (q.fiberToSpecResidueField c)
  let e := q.fiberι c
  have hemb : Topology.IsClosedEmbedding e := by
    refine ⟨IsPreimmersion.isEmbedding e, ?_⟩
    rw [Scheme.Hom.range_fiberι]
    exact hc.preimage q.continuous
  let Z : Set T := closure {x} ∩ (U : Set T)ᶜ
  have hZ : IsClosed Z := isClosed_closure.inter U.isOpen.isClosed_compl
  obtain ⟨x', hx'⟩ : x ∈ Set.range e := by
    rw [Scheme.Hom.range_fiberι]; exact hx
  have hne : (e ⁻¹' Z).Nonempty := ⟨x', by
    show e x' ∈ Z
    rw [hx']; exact ⟨subset_closure rfl, hxU⟩⟩
  obtain ⟨y, hyZ, hyc⟩ := nonempty_inter_closedPoints hne (hZ.preimage e.continuous).isLocallyClosed
  have hyc' : IsClosed ({e y} : Set T) := by
    rw [← Set.image_singleton]
    exact hemb.isClosedMap _ hyc
  have hqy : q (e y) = c := by
    have : e y ∈ Set.range e := ⟨y, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  exact hyZ.2 (hU _ hyc' hqy)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppOfFlatBaseChangeEqualisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_app_of_flat_baseChange_equalised : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y → (∀ x : Γ(S, ⊤), (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom) → ∀ V : Y.Opens, IsAffineOpen V → ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  first | exact @GlobalTheory.Mum.AffDesc.mem_range_app_of_flat | exact GlobalTheory.Mum.AffDesc.mem_range_app_of_flat | (intros; apply GlobalTheory.Mum.AffDesc.mem_range_app_of_flat <;> assumption)
end

