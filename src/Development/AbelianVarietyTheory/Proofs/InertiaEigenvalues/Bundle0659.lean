import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0572
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Formalism.LocalToGlobal.IndefiniteReal.LinksComap
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothDualNeZeroAtVector
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.SmoothForm

theorem exists_smooth_form_ne_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsSmooth ρ → ∀ v : V, v ≠ 0 → ∃ l : Module.Dual ℂ V, l ∈ smoothPart ρ.dual ∧ l v ≠ 0 := by
  intro G V _ _ _ _ _ ρ hK hρ v hv
  obtain ⟨K, hKo, hKc, hKU⟩ := hK {g | ρ g v = v} ((hρ v).mem_nhds (by simp))
  have hfix : v ∈ fixed ρ K := GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => hKU hh
  have hnot : v ∉ twKer ρ K 1 := fun h => hv (GlobalTheory.IwahoriInj.eq_zero_of_fixed hρ hKc hfix h)
  have hq : (twKer ρ K 1).mkQ v ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (V ⧸ twKer ρ K 1), f ((twKer ρ K 1).mkQ v) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  refine ⟨f ∘ₗ (twKer ρ K 1).mkQ, ?_, hf⟩
  have hinv : ∀ g ∈ K, ρ.dual g (f ∘ₗ (twKer ρ K 1).mkQ) = f ∘ₗ (twKer ρ K 1).mkQ := by
    intro g hg
    refine LinearMap.ext fun x => ?_
    rw [Representation.dual_apply]
    show f ((twKer ρ K 1).mkQ (ρ g⁻¹ x)) = f ((twKer ρ K 1).mkQ x)
    congr 1
    exact (Submodule.Quotient.eq _).2 (GlobalTheory.IwahoriInj.sub_mem_twKer (inv_mem hg) x)
  exact GlobalTheory.SmGL.mem_smoothPart_of_nhds
    (Filter.mem_of_superset (hKo.mem_nhds K.one_mem) fun g hg => hinv g hg)

end GlobalTheory.SmoothForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleHomValueMap
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem stratHom_map_mulVec {m n : Type} [Fintype n] {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A')
    (M : Matrix m n A) (v : n → A) : (fun i => φ ((M.mulVec v) i)) = (M.map φ).mulVec (fun i => φ (v i)) := by
  funext i
  exact RingHom.map_mulVec φ M v i

theorem stratHom_coord_nat {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} {S : Strat bk d}
    (Y : Matrix (Fin d') (Fin d) bk.S) {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) {Q Q' : Obj l ↥(OL K)} (r : Hom Q Q') (a : Hom B Q) (g : Hom bk.prism Q) (x : N) :
    (fun i => r.f (((Y.map (BK.hf g)).mulVec (V.v a g x)) i)) =
      (Y.map (BK.hf (r.comp g))).mulVec (V.v (r.comp a) (r.comp g) x) := by
  rw [stratHom_map_mulVec]
  have e1 : (Y.map (BK.hf g)).map r.f = Y.map (BK.hf (r.comp g)) := by
    rw [Matrix.map_map]; rfl
  have e2 : (fun i => r.f (V.v a g x i)) = V.v (r.comp a) (r.comp g) x := by
    funext i; exact (V.v_nat r a g x i).symm
  rw [e1, e2]

theorem stratHom_coord_ε {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} {S : Strat bk d}
    {S' : Strat bk d'} {Y : Matrix (Fin d') (Fin d) bk.S} (hY : IsStratHom S S' Y) {B : Obj l ↥(OL K)} {N : Type}
    [AddCommGroup N] [Module B.A N] (V : Eval S B N) {Q : Obj l ↥(OL K)} (a : Hom B Q) (g g' : Hom bk.prism Q)
    (x : N) :
    (Y.map (BK.hf g)).mulVec (V.v a g x) = (S'.ε g g').mulVec ((Y.map (BK.hf g')).mulVec (V.v a g' x)) := by
  rw [V.v_ε a g g' x, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hY.ε]

theorem evalHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d')
    (Y : Matrix (Fin d') (Fin d) bk.S), IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N]
    [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] (V : Eval S B N) (V' : Eval S' B N'),
    ∃ w : N →ₗ[B.A] N', ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : N),
      V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x) := by
  intro l _ K bk d d' S S' Y hY B N _ _ N' _ _ V V'
  obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  obtain ⟨inj, ev⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' B C N' V' h f hc
  have hz : ∀ x, ∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h →
      (fun i => p.f (((Y.map (BK.hf f)).mulVec (V.v h f x)) i)) = (S'.ε (p.comp f) (q.comp f)).mulVec
        fun i => q.f (((Y.map (BK.hf f)).mulVec (V.v h f x)) i) := by
    intro x Q p q hpq
    have e : V.v (p.comp h) (p.comp f) x = V.v (q.comp h) (p.comp f) x := by rw [hpq]
    refine (stratHom_coord_nat Y V p h f x).trans ?_
    refine Eq.trans ?_ (congrArg (S'.ε (p.comp f) (q.comp f)).mulVec (stratHom_coord_nat Y V q h f x)).symm
    rw [e]
    exact stratHom_coord_ε hY V (q.comp h) (p.comp f) (q.comp f) x
  choose w0 hw0 using fun x => ev _ (hz x)
  let w : N →ₗ[B.A] N' :=
    { toFun := w0
      map_add' := fun x y => by
        apply inj
        show V'.v h f (w0 (x + y)) = V'.v h f (w0 x + w0 y)
        refine (hw0 (x + y)).trans ?_
        refine Eq.trans ?_ ((V'.v h f).map_add (w0 x) (w0 y)).symm
        refine Eq.trans ?_ (congrArg₂ (· + ·) (hw0 x) (hw0 y)).symm
        exact (congrArg (Y.map (BK.hf f)).mulVec ((V.v h f).map_add x y)).trans (Matrix.mulVec_add _ _ _)
      map_smul' := fun c x => by
        apply inj
        show V'.v h f (w0 (c • x)) = V'.v h f (c • w0 x)
        refine (hw0 (c • x)).trans ?_
        refine Eq.trans ?_ ((V'.v h f).map_smulₛₗ c (w0 x)).symm
        refine Eq.trans ?_ (congrArg (h.f c • ·) (hw0 x)).symm
        exact (congrArg (Y.map (BK.hf f)).mulVec ((V.v h f).map_smulₛₗ c x)).trans (Matrix.mulVec_smul _ _ _) }
  refine ⟨w, fun Q a g x => ?_⟩
  obtain ⟨Q', h', a', hcomm, hinj⟩ := GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B C h hc Q a
  have hw : w x = w0 x := rfl
  funext i
  apply hinj
  have lhs : (fun j => h'.f (V'.v a g (w0 x) j)) = V'.v (a'.comp h) (h'.comp g) (w0 x) := by
    exact (funext fun j => (V'.v_nat h' a g (w0 x) j).symm).trans
      (congrArg (fun t => V'.v t (h'.comp g) (w0 x)) hcomm.symm)
  have rhs : (fun j => h'.f (((Y.map (BK.hf g)).mulVec (V.v a g x)) j)) =
      (Y.map (BK.hf (h'.comp g))).mulVec (V.v (a'.comp h) (h'.comp g) x) := by
    exact (stratHom_coord_nat Y V h' a g x).trans
      (congrArg (fun t => (Y.map (BK.hf (h'.comp g))).mulVec (V.v t (h'.comp g) x)) hcomm.symm)
  have mid : V'.v (a'.comp h) (a'.comp f) (w0 x) = (Y.map (BK.hf (a'.comp f))).mulVec (V.v (a'.comp h) (a'.comp f) x) := by
    exact (funext fun j => V'.v_nat a' h f (w0 x) j).trans
      ((congrArg (fun v : Fin d' → C.A => fun j => a'.f (v j)) (hw0 x)).trans (stratHom_coord_nat Y V a' h f x))
  have := congrFun (lhs.trans ((V'.v_ε (a'.comp h) (h'.comp g) (a'.comp f) (w0 x)).trans
    ((congrArg (S'.ε (h'.comp g) (a'.comp f)).mulVec mid).trans
      ((stratHom_coord_ε hY V (a'.comp h) (h'.comp g) (a'.comp f) x).symm.trans rhs.symm)))) i
  rw [hw]
  exact this

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleValue
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EvalEx

theorem semiBC_comp {A B C M N P : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P] {f : A →+* B} {g : B →+* C} {k : A →+* C}
    (u : M →ₛₗ[f] N) (t : N →ₛₗ[g] P) (w : M →ₛₗ[k] P) (hk : ∀ a, k a = g (f a)) (hw : ∀ x, w x = t (u x))
    (hu : SemiBC u) (ht : SemiBC t) : SemiBC w := by
  intro Q _ _ v
  letI : Module B Q := Module.compHom Q g
  let v' : M →ₛₗ[f] Q :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun a x => by
        change v (a • x) = g (f a) • v x
        rw [v.map_smulₛₗ, hk] }
  obtain ⟨z, hz, hzu⟩ := hu Q v'
  let z' : N →ₛₗ[g] Q :=
    { toFun := z
      map_add' := z.map_add
      map_smul' := fun b n => z.map_smul b n }
  obtain ⟨y, hy, hyu⟩ := ht Q z'
  refine ⟨y, fun x => by rw [hw, hy]; exact hz x, fun y' hy' => hyu y' fun n => ?_⟩
  let r : N →ₗ[B] Q :=
    { toFun := fun n => y' (t n)
      map_add' := fun n n' => by simp only [map_add]
      map_smul' := fun b n => by
        change y' (t (b • n)) = g b • y' (t n)
        rw [t.map_smulₛₗ, y'.map_smul] }
  have := hzu r fun x => by
    change y' (t (u x)) = v x
    rw [← hw]; exact hy' x
  exact LinearMap.congr_fun this n

theorem ε_mulVec {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) {B : Obj l ↥(OL K)}
    (f g h : Hom bk.prism B) (v : Fin d → B.A) :
    (S.ε f g).mulVec ((S.ε g h).mulVec v) = (S.ε f h).mulVec v := by
  rw [Matrix.mulVec_mulVec, S.ε_trans]

theorem hom_comp_assoc {l : ℕ} {R : Type} [CommRing R] {X Y Z W : Obj l R} (p : Hom Z W) (q : Hom Y Z)
    (r : Hom X Y) : (p.comp q).comp r = p.comp (q.comp r) := Hom.ext' rfl

end GlobalTheory.BSP.EvalEx

namespace GlobalTheory.BSP

theorem exists_eval : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B : Obj l ↥(OL K)), ∃ (N : Type) (_ : AddCommGroup N) (_ : Module B.A N), Nonempty (Eval S B N) := by
  intro l _ K bk d S B
  obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  obtain ⟨P, _, _, _, _, u, hu, hcoc⟩ := GlobalTheory.T.exists_finiteProjective_descent_prismCover l K bk d S B C h f hc
  have hv := GlobalTheory.T.stratifiedCoordinates_of_prismCover l K bk d S B C h f hc P u hcoc
  choose vv hvv using hv
  have po : ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q), ∃ (Q₀ : Obj l ↥(OL K)) (a₀ : Hom C Q₀) (h₀ : Hom Q Q₀),
      a₀.comp h = h₀.comp a ∧ Cover h₀ ∧ Function.Injective h₀.f := by
    intro Q a
    obtain ⟨Q₀, a₀, h₀, hpo⟩ := hc.stable.po Q a
    have hc₀ := (GlobalTheory.T.stable_and_cover_prismHom_of_pushout l _ B C Q Q₀ h a a₀ h₀ hpo).2 hc
    exact ⟨Q₀, a₀, h₀, hpo.comm, hc₀, (GlobalTheory.T.prism_cover_injective_and_descent l _ Q Q₀ h₀ hc₀).1⟩
  refine ⟨P, inferInstance, inferInstance, ⟨{
    fin := inferInstance
    proj := inferInstance
    v := fun {Q} a g => vv Q a g
    bc := ?_
    v_ε := ?_
    v_nat := ?_ }⟩⟩
  · intro Q a g
    obtain ⟨Q₀, a₀, h₀, hcomm, hc₀, -⟩ := po Q a
    have hf : ∀ y, a₀.f (h.f y) = h₀.f (a.f y) := fun y => congrArg (fun φ : Hom B Q₀ => φ.f y) hcomm
    have hE1 : S.ε (h₀.comp g) (a₀.comp f) * S.ε (a₀.comp f) (h₀.comp g) = 1 := by
      rw [S.ε_trans, S.ε_refl]
    have hE2 : S.ε (a₀.comp f) (h₀.comp g) * S.ε (h₀.comp g) (a₀.comp f) = 1 := by
      rw [S.ε_trans, S.ε_refl]
    let s : (Fin d → Q₀.A) ≃ₗ[Q₀.A] (Fin d → Q₀.A) :=
      { toFun := (S.ε (h₀.comp g) (a₀.comp f)).mulVec
        invFun := (S.ε (a₀.comp f) (h₀.comp g)).mulVec
        map_add' := Matrix.mulVec_add _
        map_smul' := fun c x => Matrix.mulVec_smul _ c x
        left_inv := fun x => by
          change (S.ε (a₀.comp f) (h₀.comp g)).mulVec ((S.ε (h₀.comp g) (a₀.comp f)).mulVec x) = x
          rw [Matrix.mulVec_mulVec, hE2, Matrix.one_mulVec]
        right_inv := fun x => by
          change (S.ε (h₀.comp g) (a₀.comp f)).mulVec ((S.ε (a₀.comp f) (h₀.comp g)).mulVec x) = x
          rw [Matrix.mulVec_mulVec, hE1, Matrix.one_mulVec] }
    let w0 : P →ₛₗ[h₀.f.comp a.f] (Fin d → Q₀.A) :=
      { toFun := fun x j => a₀.f (u x j)
        map_add' := fun x y => by funext j; simp only [map_add, Pi.add_apply]
        map_smul' := fun b x => by
          funext j
          simp only [LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.comp_apply, hf] }
    have hw0 : SemiBC w0 := EvalEx.semiBC_comp u (piMap a₀.f (Fin d)) w0 (fun y => (hf y).symm)
      (fun x => rfl) hu (semiBC_piMap a₀.f _)
    exact GlobalTheory.T.semilinear_projective_module_compose l _ Q Q₀ h₀ hc₀ B.A a.f P (Fin d → Q.A) (Fin d → Q₀.A) (vv Q a g)
      (piMap h₀.f (Fin d)) (s.toLinearMap.comp w0) (fun x => (hvv Q a g Q₀ h₀ a₀ hcomm x).symm)
      (semiBC_piMap h₀.f _) (hw0.comp_equiv s)
  · intro Q a g g' x
    obtain ⟨Q₀, a₀, h₀, hcomm, -, hinj⟩ := po Q a
    funext i
    apply hinj
    have e1 := congrFun (hvv Q a g Q₀ h₀ a₀ hcomm x) i
    have e2 := hvv Q a g' Q₀ h₀ a₀ hcomm x
    rw [e1, RingHom.map_mulVec, S.ε_nat,
      show (⇑h₀.f ∘ (vv Q a g') x) = fun i => h₀.f ((vv Q a g') x i) from rfl, e2]
    exact congrFun (EvalEx.ε_mulVec S (h₀.comp g) (h₀.comp g') (a₀.comp f) _).symm i
  · intro Q Q' c a g x i
    have hp := po Q' (c.comp a)
    obtain ⟨Q₁, a₁, h₁, hcomm, -, hinj⟩ := hp
    apply hinj
    have e1 := congrFun (hvv Q' (c.comp a) (c.comp g) Q₁ h₁ a₁ hcomm x) i
    have e2 := congrFun (hvv Q a g Q₁ (h₁.comp c) a₁ (hcomm.trans (EvalEx.hom_comp_assoc h₁ c a).symm) x) i
    have e3 : (h₁.comp c).f ((vv Q a g) x i) = h₁.f (c.f ((vv Q a g) x i)) := rfl
    refine e1.trans (Eq.trans ?_ (e3 ▸ e2).symm)
    exact congrArg (fun φ => (S.ε φ (a₁.comp f)).mulVec (fun j => a₁.f (u x j)) i)
      (EvalEx.hom_comp_assoc h₁ c g).symm

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedValueTransitionBaseChange
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem eval_transition_comp_assoc {l : ℕ} {R : Type} [CommRing R] {P P' P'' P''' : Obj l R}
    (c : Hom P'' P''') (b : Hom P' P'') (a : Hom P P') : c.comp (b.comp a) = (c.comp b).comp a :=
  Hom.ext' rfl

theorem eval_transition : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B B' : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N']
    [Module B'.A N'] (V : Eval S B N) (V' : Eval S B' N') (k : Hom B B'),
    ∃ t : N →ₛₗ[k.f] N', SemiBC t ∧ ∀ (Q : Obj l ↥(OL K)) (a : Hom B' Q) (g : Hom bk.prism Q) (x : N),
      V'.v a g (t x) = V.v (a.comp k) g x := by
  intro l _ K bk d S B B' N _ _ N' _ _ V V' k
  obtain ⟨C', h', ⟨f'⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B'
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B' C' N' V' h' f' hc
  have hz : ∀ x : N, ∃ y, V'.v h' f' y = V.v (h'.comp k) f' x := by
    intro x
    apply hsurj
    intro Q p q hpq
    have e : p.comp (h'.comp k) = q.comp (h'.comp k) := by
      rw [eval_transition_comp_assoc, hpq, ← eval_transition_comp_assoc]
    have hp : (fun i => p.f (V.v (h'.comp k) f' x i)) = V.v (p.comp (h'.comp k)) (p.comp f') x :=
      funext fun i => (V.v_nat p (h'.comp k) f' x i).symm
    have hq : (fun i => q.f (V.v (h'.comp k) f' x i)) = V.v (q.comp (h'.comp k)) (q.comp f') x :=
      funext fun i => (V.v_nat q (h'.comp k) f' x i).symm
    rw [hp, hq, V.v_ε (p.comp (h'.comp k)) (p.comp f') (q.comp f') x, e]
  choose t0 ht0 using hz
  let t : N →ₛₗ[k.f] N' :=
    { toFun := t0
      map_add' := fun x y => hinj <|
        (ht0 (x + y)).trans ((LinearMap.map_add (V.v (h'.comp k) f') x y).trans
          ((congrArg₂ (· + ·) (ht0 x) (ht0 y)).symm.trans (LinearMap.map_add (V'.v h' f') (t0 x) (t0 y)).symm))
      map_smul' := fun c x => hinj <|
        (ht0 (c • x)).trans ((LinearMap.map_smulₛₗ (V.v (h'.comp k) f') c x).trans
          ((congrArg (h'.f (k.f c) • ·) (ht0 x)).symm.trans (LinearMap.map_smulₛₗ (V'.v h' f') (k.f c) (t0 x)).symm)) }
  have hT : ∀ x, V'.v h' f' (t x) = V.v (h'.comp k) f' x := ht0
  refine ⟨t, ?_, ?_⟩
  · haveI := V.fin; haveI := V.proj; haveI := V'.fin; haveI := V'.proj
    exact GlobalTheory.T.semilinear_projective_module_compose l (↥(OL K)) B' C' h' hc B.A k.f N N' (Fin d → C'.A) t (V'.v h' f')
      (V.v (h'.comp k) f') (fun x => (hT x).symm) (V'.bc h' f') (V.bc (h'.comp k) f')
  · intro Q a g x
    obtain ⟨Q'', h'', a', hsq, hinj''⟩ := GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B' C' h' hc Q a
    have e2 : h''.comp (a.comp k) = a'.comp (h'.comp k) := by
      rw [eval_transition_comp_assoc, ← hsq, ← eval_transition_comp_assoc]
    have key : V'.v (a'.comp h') (a'.comp f') (t x) = V.v (a'.comp (h'.comp k)) (a'.comp f') x :=
      funext fun j => (V'.v_nat a' h' f' (t x) j).trans ((congrArg a'.f (congrFun (hT x) j)).trans (V.v_nat a' (h'.comp k) f' x j).symm)
    funext i
    apply hinj''
    calc h''.f (V'.v a g (t x) i) = V'.v (h''.comp a) (h''.comp g) (t x) i := (V'.v_nat h'' a g (t x) i).symm
      _ = V'.v (a'.comp h') (h''.comp g) (t x) i := congrArg (fun c => V'.v c (h''.comp g) (t x) i) hsq.symm
      _ = (S.ε (h''.comp g) (a'.comp f')).mulVec (V'.v (a'.comp h') (a'.comp f') (t x)) i :=
          congrFun (V'.v_ε (a'.comp h') (h''.comp g) (a'.comp f') (t x)) i
      _ = (S.ε (h''.comp g) (a'.comp f')).mulVec (V.v (a'.comp (h'.comp k)) (a'.comp f') x) i :=
          congrArg (fun w => (S.ε (h''.comp g) (a'.comp f')).mulVec w i) key
      _ = V.v (a'.comp (h'.comp k)) (h''.comp g) x i :=
          (congrFun (V.v_ε (a'.comp (h'.comp k)) (h''.comp g) (a'.comp f') x) i).symm
      _ = V.v (h''.comp (a.comp k)) (h''.comp g) x i := congrArg (fun c => V.v c (h''.comp g) x i) e2.symm
      _ = h''.f (V.v (a.comp k) g x i) := V.v_nat h'' (a.comp k) g x i

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtAComap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T N : Type}

def extL (L : LevCh D T) (s : N → T) (a : N → ℕ) : LevCh D (T ⊕ N) :=
  { L with
    xiH := Sum.elim L.xiH fun n => L.xiH (s n) ^ a n
    xi := Sum.elim L.xi fun n => L.xi (s n) ^ a n
    Q := Sum.elim L.Q fun n => L.Q (s n)
    xiR := Sum.elim L.xiR fun n PP => L.xiR (s n) PP ^ a n }

structure NewFam {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m) (s : N → T) where
  muVal : Fin m → N → Pl0 → Kˣ
  SR : N → CSD K
  actR : ∀ n, Representation K G (SR n).Forms
  opR : ∀ n, A.ok (s n) × ℕ → Module.End K (SR n).Forms
  SL : Fin m → N → CSD K
  actL : ∀ j n, Representation K G (SL j n).Forms
  opL : ∀ j n, A.ok (s n) × ℕ → Module.End K (SL j n).Forms

def extA {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m) {s : N → T} (X : NewFam A s) :
    FamIn K G Pl0 (T ⊕ N) m where
  v0 := A.v0
  μ0 := .inl A.μ0
  X := A.X
  r := A.r
  t := A.t
  q := A.q
  muVal j := Sum.elim (A.muVal j) (X.muVal j)
  etaVal := A.etaVal
  ok := Sum.elim A.ok fun n => A.ok (s n)
  MtildeCSD := Sum.elim A.MtildeCSD X.SR
  leftGroupActionRight τ := Sum.rec A.leftGroupActionRight X.actR τ
  heckeR τ := Sum.rec A.heckeR X.opR τ
  MtCSD j := Sum.elim (A.MtCSD j) (X.SL j)
  leftGroupActionLift j τ := Sum.rec (A.leftGroupActionLift j) (X.actL j) τ
  heckeL j τ := Sum.rec (A.heckeL j) (X.opL j) τ

theorem extA_comap {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m) {s : N → T}
    (X : NewFam A s) : (extA A X).comap Sum.inl A.μ0 = A := rfl

variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure NewReal (R : RealDat D A Ks) {s : N → T} (a : N → ℕ) (X : NewFam A s) where
  BR : ∀ n, Bridge.SideReal D D.sp.X'
    (Bridge.envOf R.cX.coef (levEnvOf D.sp.X' R.βX ((extL R.toLevCh s a).datXt (.inr n)) R.pl (A.ok (s n))))
    (X.SR n) (X.actR n) (X.opR n) (fun i => i.2)
  BL : ∀ i n, Bridge.SideReal D (Vc D i)
    (Bridge.envOf (R.cV i).coef (levEnvOf (Vc D i) (R.βV i) ((extL R.toLevCh s a).datVt i (.inr n)) R.pl (A.ok (s n))))
    (X.SL i n) (X.actL i n) (X.opL i n) (fun i => i.2)
  HX : N → HMod (Bridge.Gf D.sp.X' → R.cX.W)
  HV : ∀ i, N → HMod (Bridge.Gf (Vc D i) → (R.cV i).W)
  jX : ∀ n, (extA A X).fam.amb.FR (.inr n) →ₛₗ[D.what₂.embLL] (HX n).H
  jV : ∀ i n, (extA A X).fam.amb.FL i (.inr n) →ₛₗ[D.what₂.embLL] (HV i n).H
  νY : N → ∀ j, Measure (GA D (Yc D j))
  fdY : N → ∀ j, Set (GA D (Yc D j))
  νX : N → Measure (GA D D.sp.X')
  fdX : N → Set (GA D D.sp.X')
  νV : ∀ i, N → Measure (GA D (Vc D i))
  fdV : ∀ i, N → Set (GA D (Vc D i))
  ωY : N → ∀ k, GA D (Yc D k) × GA D (Yc D (k + 1)) →* Module.End ℂ (WO (Yc D k) (Yc D (k + 1)) → ℂ)
  ωX : N → GA D (Yc D (D.R.m - 1)) × GA D D.sp.X' →* Module.End ℂ (WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ)
  ωP : ∀ i, N → GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)
  vY : N → ∀ k, WO (Yc D k) (Yc D (k + 1)) → ℂ
  vX : N → WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ
  vP : ∀ i, N → WO (Vc D i) (Wc D i) → ℂ
  ioY : ∀ n k, MultT R.θ (R.MY (k + 1)) (levS _ (R.βY (k + 1)) ((extL R.toLevCh s a).datYt (.inr n) (k + 1) R.triv))
      (Lev.levChi _ (R.βY (k + 1)) ((extL R.toLevCh s a).datYt (.inr n) (k + 1) R.triv)) →ₗ[ℂ]
    MultT R.θ (R.MY k) (levS _ (R.βY k) ((extL R.toLevCh s a).datYt (.inr n) k R.triv))
      (Lev.levChi _ (R.βY k) ((extL R.toLevCh s a).datYt (.inr n) k R.triv))
  ioX : ∀ n, LinearMap.range (R.cX.toMap R.prX ∘ₗ (HX n).e) →ₗ[ℂ]
    MultT R.θ (R.MY (D.R.m - 1)) (levS _ (R.βY (D.R.m - 1)) ((extL R.toLevCh s a).datYt (.inr n) (D.R.m - 1) R.triv))
      (Lev.levChi _ (R.βY (D.R.m - 1)) ((extL R.toLevCh s a).datYt (.inr n) (D.R.m - 1) R.triv))
  Th : ∀ n, (HX n).H →ₗ[ℂ] R.HE.H
  thF : ∀ i n, (HV i n).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))
  thG : ∀ i n, (HV i n).H →ₗ[ℂ] (R.HW i (sg0 D A)).H

set_option maxHeartbeats 4000000 in

def extR (R : RealDat D A Ks) {s : N → T} {a : N → ℕ} {X : NewFam A s} (Y : NewReal R a X) : RealDat D (extA A X) Ks where
  toLevCh := extL R.toLevCh s a
  hv0 := R.hv0
  eG := R.eG
  pl := R.pl
  Sb := R.Sb
  θ := R.θ
  ψ := R.ψ
  MY := R.MY
  MX := R.MX
  MW := R.MW
  cX := R.cX
  cV := R.cV
  B := { R := fun τ => Sum.rec R.B.R Y.BR τ, L := fun i τ => Sum.rec (R.B.L i) (Y.BL i) τ, rankR := R.B.rankR,
         rankL := R.B.rankL }
  prX := R.prX
  HX := Sum.elim R.HX Y.HX
  HV i := Sum.elim (R.HV i) (Y.HV i)
  HE := R.HE
  HW := R.HW
  gE := R.gE
  gW := R.gW
  jX τ := Sum.rec R.jX Y.jX τ
  jV i τ := Sum.rec (R.jV i) (Y.jV i) τ
  νY := Sum.elim R.νY Y.νY
  fdY := Sum.elim R.fdY Y.fdY
  ν0 := R.ν0
  fd0 := R.fd0
  νX := Sum.elim R.νX Y.νX
  fdX := Sum.elim R.fdX Y.fdX
  νV i := Sum.elim (R.νV i) (Y.νV i)
  fdV i := Sum.elim (R.fdV i) (Y.fdV i)
  νW := R.νW
  fdW := R.fdW
  ωY := Sum.elim R.ωY Y.ωY
  ωX := Sum.elim R.ωX Y.ωX
  ωP i := Sum.elim (R.ωP i) (Y.ωP i)
  vac := R.vac
  vacX := R.vacX
  vacP := R.vacP
  vY := Sum.elim R.vY Y.vY
  vX := Sum.elim R.vX Y.vX
  vP i := Sum.elim (R.vP i) (Y.vP i)
  ItY := R.ItY
  ItX := R.ItX
  ioY τ := Sum.rec R.ioY Y.ioY τ
  ioX τ := Sum.rec R.ioX Y.ioX τ
  Th τ := Sum.rec R.Th Y.Th τ
  BV := R.BV
  ioP := R.ioP
  thF i τ := Sum.rec (R.thF i) (Y.thF i) τ
  thG i τ := Sum.rec (R.thG i) (Y.thG i) τ
  nW := R.nW
  FW := R.FW
  mu w := .inl (R.mu w)
  twPl := R.twPl
  kap := R.kap
  lam _ _ _ _ := 0
  err0 := R.err0

set_option maxHeartbeats 4000000 in
theorem extR_comap (R : RealDat D A Ks) {s : N → T} {a : N → ℕ} {X : NewFam A s} (Y : NewReal R a X) :
    (extR R Y).comap Sum.inl A.μ0 R.mu R.twPl R.FW R.kap R.lam R.err0 = R := rfl

end GlobalTheory.ConjExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldEStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSupercuspidal_comp_generalLinearGroupMapOfFieldEquiv : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i.symm → ∀ {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), GlobalTheory.SmGL.IsCuspidal π → GlobalTheory.SmGL.IsCuspidal (π.comp (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom)) := by
  first | exact @GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap | exact GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap | (intros; apply GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap <;> assumption)
end

