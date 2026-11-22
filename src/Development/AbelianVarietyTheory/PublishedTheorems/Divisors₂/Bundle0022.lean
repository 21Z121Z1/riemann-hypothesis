import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0737
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine
section
noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.Published

open GlobalTheory.EisLine in

def EisensteinResidueLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y →
      ∀ (x : Matrix (Fin n) (Fin 1) E), x = X.submatrix id (fun _ => 0) →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ h : GAd σ J → ℝ,
        (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
          ∃ k ∈ levelAll σ J L a, g = p * k) →
        (∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l) →
      ∀ T : Set (ratPts σ J), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
            (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x) →
      ∃ R : ℂ, R ≠ 0 ∧ ∀ g : GAd σ J,
        Tendsto (fun s : ℂ => (s - ((n : ℂ) - 1) / 2) * ∑' t : T, (h (t.1.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2))
          (𝓝[{s : ℂ | ((n : ℝ) - 1) / 2 < s.re}] (((n : ℂ) - 1) / 2)) (𝓝 R)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep

namespace GlobalTheory.Whittaker

section Bridge

variable {k : Type} [Field k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem superDiag_eq_sum_pairs (g : GL (Fin N) k) :
    superDiag g = ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, g.val p.1 p.2 := by
  simp only [superDiag, Finset.sum_filter, Fintype.sum_prod_type]

theorem val_whitChar (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    ((GlobalTheory.LocGL.whitChar ψ N u : ℂˣ) : ℂ) = ψ (superDiag u.1) := by
  rw [superDiag_eq_sum_pairs]; rfl

theorem isGeneric_iff_isGenericFor (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) :
    IsGeneric ψ π ↔ GlobalTheory.LocGL.IsGenericFor ψ π := by
  constructor
  · rintro ⟨l, hl, h⟩
    refine Submodule.Quotient.nontrivial_iff.2 fun htop => hl (LinearMap.ker_eq_top.1 (eq_top_iff.2 (htop ▸ ?_)))
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, val_whitChar, h u.1 u.2 v, sub_self]
  · intro h
    have h1 := Submodule.Quotient.nontrivial_iff.1 h
    obtain ⟨l, hl, hk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h1)
    refine ⟨l, hl, fun u hu v => ?_⟩
    have h2 := hk (Submodule.subset_span ⟨⟨u, hu⟩, v, rfl⟩)
    simp only [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, val_whitChar] at h2
    exact sub_eq_zero.1 h2

theorem not_isGeneric_detRep {ψ : AddChar k Circle} (hψ : ψ ≠ 1) (hN : 2 ≤ N) (χ : kˣ →* ℂˣ) :
    ¬ IsGeneric ψ (detRep (Fin N) χ) := fun h =>
  GlobalTheory.LocGL.not_isGenericFor_detRep hψ hN χ ((isGeneric_iff_isGenericFor _ _).1 h)

theorem IsGeneric.of_surjective {ψ : AddChar k Circle} {π : Representation ℂ (GL (Fin N) k) V}
    {σ : Representation ℂ (GL (Fin N) k) W} (f : π.IntertwiningMap σ) (hf : Function.Surjective f) (h : IsGeneric ψ σ) :
    IsGeneric ψ π := by
  obtain ⟨l, hl, h⟩ := h
  refine ⟨l ∘ₗ f.toLinearMap, fun e => hl (LinearMap.ext fun w => ?_), fun u hu v => ?_⟩
  · obtain ⟨v, rfl⟩ := hf w
    exact LinearMap.congr_fun e v
  · exact (congrArg l (f.isIntertwining _ _ u v)).trans (h u hu _)

end Bridge

section Exact

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem twKer_eq_twKer_twist (π : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ) :
    twKer π U θ = twKer (twist (π.comp U.subtype) θ⁻¹) ⊤ 1 := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨⟨u, trivial⟩, (θ u : ℂ) • v, ?_⟩
    simp [smul_smul]
  · rintro _ ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨u.1, (((θ u.1)⁻¹ : ℂˣ) : ℂ) • v, ?_⟩
    simp [smul_smul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem isSmoothChar_whitChar {ψ : AddChar k Circle} (hψ : Continuous ψ) : IsSmoothChar (GlobalTheory.LocGL.whitChar ψ N) := by
  obtain ⟨r, hr⟩ := GlobalTheory.SplitWeil.exists_cball_addChar_eq_one ψ hψ
  have hc : Continuous fun u : unipB k (Fin N) => superDiag u.1 :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  have h0 : superDiag ((1 : unipB k (Fin N)) : GL (Fin N) k) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj =>
      Matrix.one_apply_ne fun e => by have := (Finset.mem_filter.1 hj).2; rw [e] at this; omega
  refine (GlobalTheory.LocGL.whitChar ψ N).ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset
    (((GlobalTheory.SplitWeil.isOpen_cball r).preimage hc).mem_nhds ?_) fun u hu => Units.ext ?_)
  · rw [Set.mem_preimage, h0]
    simp [GlobalTheory.SplitWeil.cball]
  · rw [val_whitChar, hr _ hu]; rfl

open GlobalTheory.JacInj GlobalTheory.IwahoriInj in

theorem IsGeneric.of_injective {ψ : AddChar k Circle} (hψ : Continuous ψ) {σ : Representation ℂ (GL (Fin N) k) V}
    {π : Representation ℂ (GL (Fin N) k) W} (f : σ.IntertwiningMap π) (hπ : IsSmooth π) (hf : Function.Injective f)
    (h : IsGeneric ψ σ) : IsGeneric ψ π := by
  rw [isGeneric_iff_isGenericFor] at h ⊢
  refine Submodule.Quotient.nontrivial_iff.2 fun e => Submodule.Quotient.nontrivial_iff.1 h (eq_top_iff.2 fun v _ => ?_)
  rw [twKer_eq_twKer_twist] at e ⊢
  let U := unipB k (Fin N)
  let π' := twist (π.comp U.subtype) (GlobalTheory.LocGL.whitChar ψ N)⁻¹
  have hs : IsSmooth π' :=
    isSmooth_twist (ρ := π.comp U.subtype) (fun w => (hπ w).preimage continuous_subtype_val) (isSmoothChar_whitChar hψ).inv
  have key : ∀ w ∈ twKer π' ⊤ 1, ∀ᶠ M : ℕ in Filter.atTop,
      w ∈ twKer π' ((grp k (conc_wt (points (Fin N)) M)).subgroupOf U) 1 := fun w hw => by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, w, rfl⟩ := hx
      filter_upwards [eventually_mem_grp (points (Fin N)) u.1.2] with M hM
      simpa using sub_mem_twKer (π := π') (H := (grp k (conc_wt (points (Fin N)) M)).subgroupOf U) hM w
    | zero => simp
    | add x y _ _ hx hy => filter_upwards [hx, hy] with M h1 h2 using add_mem h1 h2
    | smul a x _ hx => filter_upwards [hx] with M h1 using Submodule.smul_mem _ a h1
  obtain ⟨M, hM⟩ := (key (f v) (e ▸ Submodule.mem_top)).exists
  have hc : IsCompact (((grp k (conc_wt (points (Fin N)) M)).subgroupOf U : Subgroup U) : Set U) :=
    (isClosed_unipRad (k := k) (points (Fin N))).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_grp (conc_wt (points (Fin N)) M))
  exact twKer_mono le_top (mem_twKer_of_map (twistMap (compMap f U.subtype) _) hs hf hc hM)

theorem IsGeneric.of_isSubquotient {ψ : AddChar k Circle} (hψ : Continuous ψ) {σ : Representation ℂ (GL (Fin N) k) V}
    {π : Representation ℂ (GL (Fin N) k) W} (hπ : IsSmooth π) (hs : IsSubquotient σ π) (h : IsGeneric ψ σ) :
    IsGeneric ψ π := by
  obtain ⟨S, f, hf⟩ := hs
  exact (h.of_surjective f hf).of_injective hψ ⟨S.toSubmodule.subtype, fun _ => rfl⟩ hπ Subtype.val_injective

end Exact

end GlobalTheory.Whittaker

namespace GlobalTheory.Published

open GlobalTheory.Whittaker

def CuspidalGeneric : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) Circle), Continuous ψ → ψ ≠ 1 →
    GlobalTheory.Whittaker.IsGeneric ψ (π.locRep w)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic in

theorem cuspidalGeneric_holds : CuspidalGeneric := by
  intro E _ _ _ a _ P w ψ' hc' h1'
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have hg : ∀ v : P.V, Good ψ (a - 1) v.1.1 := fun v => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ v.1 (P.cusp _ v.2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  have := Submodule.nontrivial_iff_ne_bot.2 P.ne_bot
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : P.V)
  have hv1 : v₀.1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w g₀
  have hrt : ∀ u (v : P.V) x, whit ψ (a - 1) (P.locRep w u v).1.1 x =
      whit ψ (a - 1) v.1.1 (x * finGL E a (locGL E a w u)) := fun u v x => whit_rt _ _ _ _
  let l : P.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) v.1.1 h
      map_add' := fun v v' => congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => congrFun (whit_smul (a - 1) c v.1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) v.1.1 h := fun _ => rfl
  have hne : l (P.locRep w gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hgen : GlobalTheory.Whittaker.IsGeneric (locPsi hψ w) (P.locRep w) := by
    refine ⟨l, fun e => hne (by rw [e]; rfl), fun u hu v => ?_⟩
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
    obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3, superDiag_eq_sum_pairs]
    rfl
  have hcont : Continuous (locPsi hψ w) := by
    refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  have hne1 : locPsi hψ w ≠ 1 := fun h1 => by
    obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  exact (isGeneric_iff_isGenericFor _ _).2 ((GlobalTheory.LocGL.isGenericFor_iff_of_continuous hcont hne1 hc' h1' _).1
    ((isGeneric_iff_isGenericFor _ _).1 hgen))

def GenericityGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (N c : ℕ) (m : Fin c → ℕ) (e : (Σ a, Fin (m a)) ≃ Fin N) (W : Type) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (Levi k fun a => Fin (m a)) W), IsSmooth ρ → GlobalTheory.Whittaker.IsGeneric ψ (parInd e ρ) →
      ∃ l : Module.Dual ℂ W, l ≠ 0 ∧ ∀ u : Levi k fun a => Fin (m a), (∀ a, u a ∈ unipB k (Fin (m a))) →
        ∀ v, l (ρ u v) = (∏ a, (ψ (superDiag (u a)) : ℂ)) * l v

def WhittakerHeredity : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ N : ℕ,
    (∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) V)
      (π : Representation ℂ (GL (Fin N) k) W) (f : σ.IntertwiningMap π), IsSmooth π → Function.Injective f →
      GlobalTheory.Whittaker.IsGeneric ψ σ → GlobalTheory.Whittaker.IsGeneric ψ π) ∧
    ∀ (c : ℕ) (m : Fin c → ℕ) (e : (Σ a, Fin (m a)) ≃ Fin N) (W : Type) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (Levi k fun a => Fin (m a)) W), IsSmooth ρ → GlobalTheory.Whittaker.IsGeneric ψ (parInd e ρ) →
      ∃ l : Module.Dual ℂ W, l ≠ 0 ∧ ∀ u : Levi k fun a => Fin (m a), (∀ a, u a ∈ unipB k (Fin (m a))) →
        ∀ v, l (ρ u v) = (∏ a, (ψ (superDiag (u a)) : ℂ)) * l v

namespace GenericityGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem block_le_one (H : GenericityGL) {ψ : AddChar k Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1) {N c : ℕ} {m : Fin c → ℕ}
    (e : (Σ a, Fin (m a)) ≃ Fin N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (Levi k fun a => Fin (m a)) W} (hρ : IsSmooth ρ) {σ : Representation ℂ (GL (Fin N) k) V}
    (hs : IsSubquotient σ (parInd e ρ)) (hg : GlobalTheory.Whittaker.IsGeneric ψ σ) (a : Fin c)
    (ha : ∀ u ∈ unipB k (Fin (m a)), ∀ v, ρ (Pi.mulSingle a u) v = v) : m a ≤ 1 := by
  by_contra hm
  obtain ⟨l, hl, h⟩ := H k ψ hc h1 N c m e W ρ hρ (hg.of_isSubquotient hc (isSmooth_parInd e ρ) hs)
  obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
    by_contra h0
    push Not at h0
    exact hl (LinearMap.ext h0)
  refine not_isGeneric_detRep h1 (N := m a) (by omega) 1
    ⟨LinearMap.id, fun e => one_ne_zero (LinearMap.congr_fun e 1), fun u hu x => ?_⟩
  have h2 := h (Pi.mulSingle a u) (fun b => by
    by_cases hb : b = a
    · subst hb; simpa using hu
    · rw [Pi.mulSingle_eq_of_ne hb]; exact one_mem _) v
  have h3 : ∀ b, superDiag (1 : GL (Fin (m b)) k) = 0 := fun b =>
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj =>
      Matrix.one_apply_ne fun e => by have := (Finset.mem_filter.1 hj).2; rw [e] at this; omega
  rw [Finset.prod_eq_single a (fun b _ hb => by rw [Pi.mulSingle_eq_of_ne hb, h3]; simp) (by simp),
    Pi.mulSingle_eq_same, ha u hu] at h2
  rw [(mul_eq_right₀ hv).1 h2.symm]
  simp [detRep]

end GenericityGL

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsModerateFormAdd
section
noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisLine
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisLineModel

open Formalism.BasicNotions in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem data_inhabited : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (X Y : Matrix (Fin 2) (Fin (0 + 1)) E) (L : Submodule (𝓞 E) (Fin 2 → E))
    (a : GL (Fin 2) (AF F ⊗[F] E)), IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧ IsHermND σ J ∧
      IsWittFrame σ J X Y ∧ IsAdapted σ J X Y L a := by
  obtain ⟨D⟩ := GlobalTheory.Mem.nonempty_record
  obtain ⟨L, a, h⟩ := exists_isAdapted_plane D.sp.cm.sig
  refine ⟨_, _, _, _, _, _, _, D.sp.cm.sig, _, _, _, L, a, isCMExt_host D, GlobalTheory.InertOfConj.unram D, ⟨fun i j => ?_, ?_⟩,
    isWittFrame_plane, h⟩
  · fin_cases i <;> fin_cases j <;> simp
  · simp [det_fin_two]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem pos {x : Matrix (Fin n) (Fin 1) E} {K : Subgroup (GAd σ J)} {h : GAd σ J → ℝ}
    (h1 : ∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧ ∃ k ∈ K, g = p * k)
    (h2 : ∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → ∀ k ∈ K, h (p * k) = absE F E l) :
    (∀ g, 0 < h g) ∧ h 1 = 1 := by
  refine ⟨fun g => ?_, by simpa using h2 1 1 (by simp) 1 (one_mem _)⟩
  obtain ⟨p, l, hp, k, hk, rfl⟩ := h1 g
  rw [h2 p l hp k hk]
  exact_mod_cast GlobalTheory.Doubling.hom_pos _ _

theorem exists_h {x y : Matrix (Fin n) (Fin 1) E} (hxy : cT (σ : E →+* E) y * J * x = 1) {K : Subgroup (GAd σ J)}
    (hK : IsCompact (K : Set (GAd σ J))) : ∃ h : GAd σ J → ℝ, ∀ p, ∀ l : (AF F ⊗[F] E)ˣ,
      (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → ∀ k ∈ K, h (p * k) = absE F E l := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  let φ : GAd σ J → AF F ⊗[F] E := fun p => (adMat F (cT (σ : E →+* E) y * J) * ((matHom _ σ J p).1 * adMat F x)) 0 0
  have hφ : ∀ p (l : AF F ⊗[F] E), (matHom _ σ J p).1 * adMat F x = l • adMat F x → φ p = l := fun p l e => by
    simp only [φ, e, Matrix.mul_smul, adMat, ← Matrix.map_mul, hxy]
    simp
  have hm : Continuous fun p : GAd σ J => (matHom _ σ J p).1 := Units.continuous_val.comp continuous_subtype_val
  have cφ : Continuous φ := (continuous_const.matrix_mul (hm.matrix_mul continuous_const)).matrix_elem 0 0
  let Q : GAd σ J → Prop := fun p => (matHom _ σ J p).1 * adMat F x = φ p • adMat F x
  have hmul : ∀ p q, Q p → Q q → (matHom _ σ J (p * q)).1 * adMat F x = (φ p * φ q) • adMat F x := fun p q hp hq => by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hp, smul_smul, mul_comm]
  have hQ : ∀ p q, Q p → Q q → Q (p * q) := fun p q hp hq => by
    have := hmul p q hp hq
    rw [← hφ _ _ this] at this; exact this
  have h1 : φ 1 = 1 := hφ 1 1 (by simp)
  let P : Subgroup (GAd σ J) :=
    { carrier := {p | Q p ∧ Q p⁻¹}
      one_mem' := by simp [Q, h1]
      mul_mem' := fun {p q} hp hq => ⟨hQ _ _ hp.1 hq.1, by rw [_root_.mul_inv_rev]; exact hQ _ _ hq.2 hp.2⟩
      inv_mem' := fun {p} hp => ⟨hp.2, by rw [inv_inv]; exact hp.1⟩ }
  have hi : ∀ p : P, φ p * φ (p : GAd σ J)⁻¹ = 1 := fun p => by
    rw [← hφ _ _ (hmul _ _ p.2.1 p.2.2), mul_inv_cancel, h1]
  let u : P →* (AF F ⊗[F] E)ˣ :=
    { toFun := fun p => ⟨φ p, φ (p : GAd σ J)⁻¹, hi p, by rw [mul_comm]; exact hi p⟩
      map_one' := Units.ext h1
      map_mul' := fun p q => Units.ext (hφ _ _ (hmul _ _ p.2.1 q.2.1)) }
  have cu : Continuous u := Units.continuous_iff.2
    ⟨cφ.comp continuous_subtype_val, cφ.comp continuous_subtype_val.inv⟩
  have cQ : IsClosed {p | Q p} := isClosed_eq (hm.matrix_mul continuous_const) (cφ.smul continuous_const)
  have cP : IsClosed (P : Set (GAd σ J)) := cQ.inter (cQ.preimage continuous_inv)
  have ht := GlobalTheory.Doubling.triv_of_isCompact (δ := (absE F E).comp u) cP (GlobalTheory.Doubling.continuous_absE.comp cu) hK
  refine ⟨fun g => GlobalTheory.Doubling.iwAbs ((absE F E).comp u) K g, fun p l hp k hk => ?_⟩
  have hp' : (matHom _ σ J p⁻¹).1 * adMat F x = l⁻¹.1 • adMat F x := by
    have := congrArg (fun z => l⁻¹.1 • ((matHom _ σ J p⁻¹).1 * z)) hp
    simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_smul, smul_smul] at this
    simpa using this.symm
  have hP : p ∈ P := ⟨by have := hp; rw [← hφ _ _ hp] at this; exact this, by have := hp'; rw [← hφ _ _ hp'] at this; exact this⟩
  have := GlobalTheory.Doubling.iwAbs_mul_of_triv ht ⟨p, hP⟩ hk
  have e : u ⟨p, hP⟩ = l := Units.ext (hφ _ _ hp)
  simp only [MonoidHom.comp_apply, e] at this
  exact congrArg NNReal.toReal this

theorem exists_h_levelAll (hc : IsCMExt F E σ) {x y : Matrix (Fin n) (Fin 1) E} (hxy : cT (σ : E →+* E) y * J * x = 1)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (a : GL (Fin n) (AF F ⊗[F] E)) :
    ∃ h : GAd σ J → ℝ, ∀ p, ∀ l : (AF F ⊗[F] E)ˣ,
      (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l :=
  exists_h hxy (GlobalTheory.Doubling.isCompact_levelAll hc _ _ _)

theorem isModerateForm_add {μ ν : (GAd σ J → ℂ) →ₗ[ℂ] ℂ} (hμ : IsModerateForm σ J μ) (hν : IsModerateForm σ J ν) :
    IsModerateForm σ J (μ + ν) := fun N => by
  obtain ⟨S, C, h1, h2⟩ := hμ N
  obtain ⟨S', C', h1', h2'⟩ := hν N
  refine ⟨S ++ S', C + C', fun l hl => (List.mem_append.1 hl).elim (h1 l) (h1' l), fun f hf hB hS => ?_⟩
  exact (norm_add_le _ _).trans (add_le_add (h2 f hf hB fun l hl => hS l (List.mem_append_left _ hl))
    (h2' f hf hB fun l hl => hS l (List.mem_append_right _ hl)))

theorem eisensteinIsotropicLine_of_isWittFrame (hP : GlobalTheory.Published.EisensteinIsotropicLine) (hc : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E))
    (hJ : IsHermND σ J) {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y)
    {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)} (hA : IsAdapted σ J X Y L a) {h : GAd σ J → ℝ}
    (h1 : ∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F (X.submatrix id fun _ : Fin 1 => 0) =
      l.1 • adMat F (X.submatrix id fun _ : Fin 1 => 0) ∧ ∃ k ∈ levelAll σ J L a, g = p * k)
    (h2 : ∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F (X.submatrix id fun _ : Fin 1 => 0) =
      l.1 • adMat F (X.submatrix id fun _ : Fin 1 => 0) → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l) :
    ∃ (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ), MeromorphicOn c Set.univ ∧ (∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, c s ≠ 0) ∧
      ∀ g s₀, MeromorphicAt (fun s => Eis s g) s₀ := by
  obtain ⟨Eis, c, -, -, h3, h4, h5⟩ := hP F E σ hc hu n J hJ r X Y hW _ _ rfl rfl L a hA h h1 h2
  refine ⟨Eis, c, h3, fun s₀ => (h5 s₀).mono fun s hs => left_ne_zero_of_mul_eq_one hs.1, fun g s₀ => ?_⟩
  obtain ⟨k, U, H, hU, e, -, hd⟩ := h4 s₀
  have a1 : AnalyticAt ℂ (fun s => H s g) s₀ := (hd _ (isModerateForm_proj σ J g)).analyticAt hU
  have a2 : MeromorphicAt (fun s => H s g / (s - s₀) ^ k) s₀ :=
    a1.meromorphicAt.fun_div (by fun_prop)
  refine a2.congr ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with s hs hs'
  rw [e s hs hs' g, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.2 hs'))]

end GlobalTheory.EisLineModel

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar

namespace GlobalTheory.Published

def LanglandsSquareIntegrable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
          ∀ (T : Finset (Fin r)) (φ : GAd σ J → ℂ), IsAutOn σ J X Y T K φ →
            (IsSqIntOn σ J X Y T φ ↔ ∀ S, T ⊆ S → ∀ s, IsCuspExp σ J X Y S K φ s → NegExp S T s)

def LanglandsLemmaUnitary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
          ∀ (T : Finset (Fin r)) (φ : GAd σ J → ℂ), IsAutOn σ J X Y T K φ →
            (∀ S, T ⊆ S → ∃! φc, IsCuspComp σ J X Y S K φ φc) ∧
            ((∀ S, T ⊆ S → IsCuspComp σ J X Y S K φ 0) → φ = 0) ∧
            (φ ≠ 0 → ∃ S, T ⊆ S ∧ ∃ s, IsCuspExp σ J X Y S K φ s)

def AutomorphicFormsUnitary : Prop := LanglandsSquareIntegrable ∧ LanglandsLemmaUnitary

end GlobalTheory.Published

namespace GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {K : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ}

theorem isSqInt_iff (H : GlobalTheory.Published.LanglandsSquareIntegrable) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (hK : IsMaxCpt σ J K) (hφ : IsAut σ J K φ) :
    IsSqInt σ J φ ↔ ∀ S s, IsCuspExp σ J X Y S K φ s → ∀ k ∈ S, ∑ i with i ≤ k, (s i).re < 0 := by
  simpa only [isSqIntOn_empty, negExp_empty, Finset.empty_subset, forall_const] using
    H F E σ h n J hJ r X Y hW K hK ∅ φ (isAutOn_empty.2 hφ)

theorem IsAutOn.isConstAlong_self {S : Finset (Fin r)} (hφ : IsAutOn σ J X Y S K φ) : IsConstAlong σ J X S φ φ :=
  fun μ 𝓕 _ _ h1 g => by simp [fun u : unip σ J X S => hφ.leftN u u.2 g, Measure.real, h1]

omit [NumberField E] in

theorem isConstAlong_empty {c : GAd σ J → ℂ} (hc : IsConstAlong σ J X ∅ φ c) : c = φ := by
  unfold IsConstAlong at hc
  rw [unip_empty] at hc
  haveI : Finite (⊥ : Subgroup (GAd σ J)) := inferInstance
  haveI : Subsingleton ((ratPts σ J).subgroupOf ⊥) := inferInstance
  have e : (Measure.haarMeasure ⊤ : Measure (⊥ : Subgroup (GAd σ J))) Set.univ = 1 := Measure.haarMeasure_self
  funext g
  rw [hc (Measure.haarMeasure ⊤) Set.univ inferInstance
    ⟨nullMeasurableSet_univ, .of_forall fun _ => ⟨1, trivial⟩, Subsingleton.pairwise⟩ e g]
  simp [fun u : (⊥ : Subgroup (GAd σ J)) => Subgroup.mem_bot.1 u.2, Measure.real, e]

theorem isCuspComp_self (H : GlobalTheory.Published.LanglandsLemmaUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (hK : IsMaxCpt σ J K) (hφ : IsCuspOn σ J X Y ∅ K φ) : IsCuspComp σ J X Y ∅ K φ φ := by
  obtain ⟨_, ⟨-, c, h1, h2⟩, -⟩ := (H F E σ h n J hJ r X Y hW K hK ∅ φ hφ.1).1 ∅ le_rfl
  obtain rfl := isConstAlong_empty h1
  exact ⟨hφ, c, h1, fun ψ hψ μ 𝓕 a b g g' => ⟨(h2 ψ hψ μ 𝓕 a b g g').1, (h2 ψ hψ μ 𝓕 a b g g').1, rfl⟩⟩

example (H : GlobalTheory.Published.LanglandsSquareIntegrable) (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin 0) E}
    (hW : IsWittFrame σ J X Y) (hK : IsMaxCpt σ J K) (hφ : IsAut σ J K φ) : IsSqInt σ J φ :=
  (isSqInt_iff H h hJ hW hK hφ).2 fun _ _ _ k => k.elim0

end GlobalTheory.StdPar

end
end

