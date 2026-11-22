import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueLat
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueFrame
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

section FrameGeneric

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

def IsFrameAt (A : Subalgebra ℤ Ω) (r : ℕ) (M : AddSubgroup E) (h : Ω) : Prop :=
  ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    ∀ e, (∃ n : ℕ, h ^ n • e ∈ M) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, h ^ n * a q ∈ A) ∧ e = ∑ q, a q • b q

theorem exists_frame_cover (A : Subalgebra ℤ Ω) (r : ℕ) (M : AddSubgroup E)
    (hloc : ∀ Q : Ideal A, Q.IsMaximal →
      ∃ h : Ω, ∃ hh : h ∈ A, (⟨h, hh⟩ : A) ∉ Q ∧ IsFrameAt A r M h) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ A) ∧ (∀ l, c l ∈ A) ∧ ∑ l, c l * f l = 1 ∧
      ∀ l, IsFrameAt A r M (f l) := by
  let H : Set A := {h | IsFrameAt A r M h}
  have htop : Ideal.span H = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨h, hh, hQh, hfr⟩ := hloc Q hQ
    exact hQh (hle (Ideal.subset_span (show (⟨h, hh⟩ : A) ∈ H from hfr)))
  have h1 : (1 : A) ∈ Ideal.span H := by rw [htop]; exact Submodule.mem_top
  obtain ⟨k, c, g, hcg⟩ := Submodule.mem_span_set'.1 h1
  refine ⟨k, fun l => ((g l : A) : Ω), fun l => (c l : Ω), fun l => (g l : A).2, fun l => (c l).2,
    ?_, fun l => (g l).2⟩
  have := congrArg Subtype.val hcg
  simpa using this

theorem mem_ideal_of_sum {A : Subalgebra ℤ Ω} (Q : Ideal A) {k : ℕ} (a y : Fin k → Ω)
    (ha : ∀ l, a l ∈ A) (hy : ∀ l, y l ∈ A) (hyQ : ∀ l, (⟨y l, hy l⟩ : A) ∈ Q) {z : Ω}
    (hz : z ∈ A) (hsum : ∑ l, a l * y l = z) : (⟨z, hz⟩ : A) ∈ Q := by
  have : (⟨z, hz⟩ : A) = ∑ l, (⟨a l, ha l⟩ : A) * ⟨y l, hy l⟩ := Subtype.ext (by simp [← hsum])
  rw [this]
  exact Q.sum_mem fun l _ => Q.mul_mem_left _ (hyQ l)

theorem intCast_subtype (A : Subalgebra ℤ Ω) (z : ℤ) :
    (⟨(z : Ω), intCast_mem A z⟩ : A) = (z : A) :=
  Subtype.ext (by simp)

theorem mem_of_prime_pow_mul_mem {A : Subalgebra ℤ Ω} {p : ℕ} (hp : p.Prime) {s : ℤ}
    (hs : ¬ (p : ℤ) ∣ s) (N : ℕ) {y : Ω} (h1 : (((p : ℤ) : Ω)) ^ N * y ∈ A)
    (h2 : (s : Ω) * y ∈ A) : y ∈ A := by
  have hcop : IsCoprime ((p : ℤ) ^ N) s := by
    have : IsCoprime (p : ℤ) s := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : ¬ p ∣ s.natAbs := fun h => hs (Int.natCast_dvd.mpr h)
      simpa [Int.gcd] using (Nat.Prime.coprime_iff_not_dvd hp).mpr this
    exact this.pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have : y = (u : Ω) * ((((p : ℤ) : Ω)) ^ N * y) + (v : Ω) * ((s : Ω) * y) := by
    have h := congrArg (Int.cast : ℤ → Ω) huv
    push_cast at h ⊢
    linear_combination (-y) * h
  rw [this]
  exact add_mem (mul_mem (intCast_mem A u) h1) (mul_mem (intCast_mem A v) h2)

end FrameGeneric

section FrameGlue

variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
  {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}

theorem frame_away {i : τ} (hi : x i ≠ 0)
    (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (Q : Ideal (chartRing ℤ x i))
    (hQ : Q.IsPrime) (hmQ : ((primeProd S : ℤ) : chartRing ℤ x i) ∉ Q) :
    ∃ h : Ω, ∃ hh : h ∈ chartRing ℤ x i, (⟨h, hh⟩ : chartRing ℤ x i) ∉ Q ∧
      IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) h := by
  classical
  set m : ℤ := primeProd S with hm
  obtain ⟨hm0, hminv⟩ := inv_prod_mem_chartRing x o₀ (S := S) i
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := B₀.frame i hi
  obtain ⟨t, ht, htf⟩ := exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers m) f hf
  obtain ⟨t', ht', htc⟩ := exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers m) c hc
  obtain ⟨J, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht
  obtain ⟨J', rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht'
  have hmA : (m : Ω) ∈ chartRing ℤ x i := intCast_mem (chartRing ℤ x i) m
  have hJ : ∀ l, (m : Ω) ^ J * f l ∈ chartRing ℤ x i := fun l => by simpa using htf l
  have hφ : ∀ l, (m : Ω) ^ (J + 1) * f l ∈ chartRing ℤ x i := fun l => by
    have : (m : Ω) ^ (J + 1) * f l = (m : Ω) * ((m : Ω) ^ J * f l) := by ring
    rw [this]; exact mul_mem hmA (hJ l)
  have hex : ∃ l, (⟨(m : Ω) ^ (J + 1) * f l, hφ l⟩ : chartRing ℤ x i) ∉ Q := by
    by_contra hall
    push Not at hall
    have hmem := mem_ideal_of_sum Q (fun l => ((m ^ J' : ℤ) : Ω) * c l)
      (fun l => (m : Ω) ^ (J + 1) * f l) htc hφ hall (z := ((m ^ (J + 1 + J') : ℤ) : Ω))
      (intCast_mem (chartRing ℤ x i) _) (by
        have : ∑ l, ((m ^ J' : ℤ) : Ω) * c l * ((m : Ω) ^ (J + 1) * f l) =
            ((m : Ω) ^ J' * (m : Ω) ^ (J + 1)) * ∑ l, c l * f l := by
          rw [Finset.mul_sum]; push_cast; exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, hsum]; push_cast; ring)
    rw [intCast_subtype] at hmem
    push_cast at hmem
    exact hmQ (hQ.mem_of_pow_mem _ hmem)
  obtain ⟨l, hl⟩ := hex
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  refine ⟨_, hφ l, hl, b, hli, hsp, fun e => ?_⟩
  have hYX : ∀ v ∈ B₀.lat i, ∃ k : ℕ, (m : Ω) ^ k • v ∈ glueLat B₀ Bp i := fun v hv => by
    obtain ⟨n, hn⟩ := (mem_B₀_iff hSR v).1 hv
    rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow] at hn
    exact ⟨n, hn⟩
  rw [exists_pow_smul_mem_iff_of_loc (chartRing ℤ x i) (glueLat B₀ Bp i) (B₀.lat i) J hm0 hmA (hJ l)
    (glueLat_stable i) (fun e he => ((mem_glueLat B₀ Bp).1 he).1)
    (fun e he => smul_mem_of_chart B₀ hminv he) hYX e, hiff e]
  refine exists_congr fun a => and_congr (forall_congr' fun q => ?_) Iff.rfl
  have key := exists_pow_smul_mem_iff_of_loc (E := Ω) (chartRing ℤ x i) (chartRing ℤ x i).toSubring.toAddSubgroup
    (chartRing o₀ x i).toSubring.toAddSubgroup J hm0 hmA (hJ l)
    (fun a ha e he => show a * e ∈ chartRing ℤ x i from mul_mem ha he) (fun y hy => mem_chartRing_of_int x i o₀ hy)
    (fun y hy => show _ * y ∈ chartRing o₀ x i from mul_mem hminv hy)
    (fun y hy => by
      obtain ⟨t, ht, hty⟩ := exists_mul_mem_chartRing_int x i o₀ (Submonoid.powers m) hy
      obtain ⟨K, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht
      exact ⟨K, by simpa using hty⟩) (a q)
  simpa [smul_eq_mul] using key.symm

end FrameGlue

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.GlueBundlesSecondOfFirstAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem SectionNef.glueBundles_second_of_first (h : _root_.GroundTheory.Heights₂.Heights.Model.SectionNef.Statement) :
    SectionNef.Statement := by
  intro κ _ _ ι _ F _ P hP hd a ha
  have hs : ∃ s : MRing ι F, IsMultiHomog s a ∧ s ∉ P := by
    rcases ha with h1 | h2
    · exact h1
    · exact h2 P hP le_rfl
  obtain ⟨s, hsa, hsP⟩ := hs
  exact h κ ι F P hP hd (fun k => (a k : ℤ)) s 1
    (_root_.GroundTheory.Heights₂.Heights.Model.isRegularSection_form hP.isPrime hsa hsP)

theorem SectionNef.equiv :
    (_root_.GroundTheory.Heights₂.Heights.Model.SectionNef.Statement ∧
      _root_.GroundTheory.Heights₂.Heights.Model.SectionNefGenerated.Statement) ↔
      SectionNef.Statement :=
  ⟨fun h => SectionNef.glueBundles_second_of_first h.1, fun _ =>
    ⟨_root_.GroundTheory.Heights₂.Heights.Model.SectionNef.proof,
      _root_.GroundTheory.Heights₂.Heights.Model.SectionNefGenerated.proof⟩⟩

theorem SectionNef.sectionNef_of_first : SectionNef.Statement :=
  SectionNef.glueBundles_second_of_first _root_.GroundTheory.Heights₂.Heights.Model.SectionNef.proof

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBundlesAgree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace BundlesAgree

variable {X : Scheme.{0}} [IsIntegral X]

lemma section_eq_zero (E : X.Modules) {U : X.Opens} (hU : genericPoint X ∉ U) (s : Γ(E, U)) :
    s = 0 := by
  have hU' : U = ⊥ := by
    by_contra h
    obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty U).mp h
    exact hU (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩)
  have ht := TopCat.Sheaf.isTerminalOfEqEmpty ⟨E.presheaf, E.isSheaf⟩ hU'
  have h0 : (𝟙 (E.presheaf.obj (op U))) = 0 := ht.hom_ext _ _
  simpa using ConcreteCategory.congr_hom h0 s

lemma section_ext (E : X.Modules)
    (hE : ∀ (U : X.Opens) (hU : genericPoint X ∈ U),
      Function.Injective (E.presheaf.germ U (genericPoint X) hU))
    {U : X.Opens} {a b : Γ(E, U)}
    (h : ∀ hU : genericPoint X ∈ U,
      E.presheaf.germ U (genericPoint X) hU a = E.presheaf.germ U (genericPoint X) hU b) :
    a = b := by
  by_cases hU : genericPoint X ∈ U
  · exact hE U hU (h hU)
  · rw [section_eq_zero E hU a, section_eq_zero E hU b]

omit [IsIntegral X] in

lemma germ_smul' (E : X.Modules) (U : X.Opens) (x : X) (hx : x ∈ U) (r : Γ(X, U)) (s : Γ(E, U)) :
    E.presheaf.germ U x hx (r • s) = X.presheaf.germ U x hx r • E.presheaf.germ U x hx s :=
  PresheafOfModules.germ_smul (R := X.presheaf) (M := E.val) x U hx r s

def lift (E E' : X.Modules)
    (φ : E.presheaf.stalk (genericPoint X) →ₗ[X.presheaf.stalk (genericPoint X)]
      E'.presheaf.stalk (genericPoint X))
    (hex : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)), ∃ t : Γ(E', U),
      E'.presheaf.germ U (genericPoint X) hU t = φ (E.presheaf.germ U (genericPoint X) hU s))
    (U : X.Opens) (s : Γ(E, U)) : Γ(E', U) :=
  haveI := Classical.dec (genericPoint X ∈ U)
  if hU : genericPoint X ∈ U then (hex U hU s).choose else 0

variable (E E' : X.Modules)
  (φ : E.presheaf.stalk (genericPoint X) →ₗ[X.presheaf.stalk (genericPoint X)]
    E'.presheaf.stalk (genericPoint X))
  (hex : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)), ∃ t : Γ(E', U),
    E'.presheaf.germ U (genericPoint X) hU t = φ (E.presheaf.germ U (genericPoint X) hU s))
  (hE' : ∀ (U : X.Opens) (hU : genericPoint X ∈ U),
      Function.Injective (E'.presheaf.germ U (genericPoint X) hU))

lemma germ_lift (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)) :
    E'.presheaf.germ U (genericPoint X) hU (lift E E' φ hex U s) =
      φ (E.presheaf.germ U (genericPoint X) hU s) := by
  rw [lift, dif_pos hU]
  exact (hex U hU s).choose_spec

include hE' in
lemma lift_add (U : X.Opens) (a b : Γ(E, U)) :
    lift E E' φ hex U (a + b) = lift E E' φ hex U a + lift E E' φ hex U b :=
  section_ext E' hE' fun hU => by
    rw [map_add, germ_lift, germ_lift, germ_lift, map_add, map_add]

include hE' in
lemma lift_zero (U : X.Opens) : lift E E' φ hex U 0 = 0 :=
  section_ext E' hE' fun hU => by
    rw [germ_lift, map_zero, map_zero, map_zero]

include hE' in
lemma lift_smul (U : X.Opens) (r : Γ(X, U)) (s : Γ(E, U)) :
    lift E E' φ hex U (r • s) = r • lift E E' φ hex U s :=
  section_ext E' hE' fun hU => by
    rw [germ_lift, germ_smul', germ_smul', map_smul, germ_lift]

include hE' in
lemma lift_res {U V : X.Opens} (i : V ⟶ U) (s : Γ(E, U)) :
    lift E E' φ hex V (E.presheaf.map i.op s) = E'.presheaf.map i.op (lift E E' φ hex U s) :=
  section_ext E' hE' fun hV => by
    rw [germ_lift, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, germ_lift]

include hE' in

def homOfGeneric : E ⟶ E' :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := lift E E' φ hex U.unop
          map_zero' := lift_zero E E' φ hex hE' U.unop
          map_add' := lift_add E E' φ hex hE' U.unop }
      naturality := fun U V i => by
        ext s
        exact lift_res E E' φ hex hE' i.unop s }
    (fun U r s => lift_smul E E' φ hex hE' U.unop r s)

include hE' in
lemma germ_homOfGeneric_app (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)) :
    E'.presheaf.germ U (genericPoint X) hU ((homOfGeneric E E' φ hex hE').app U s) =
      φ (E.presheaf.germ U (genericPoint X) hU s) :=
  germ_lift E E' φ hex U hU s

include hE' in

lemma hom_ext_of_germ {f g : E ⟶ E'}
    (h : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)),
      E'.presheaf.germ U (genericPoint X) hU (f.app U s) =
        E'.presheaf.germ U (genericPoint X) hU (g.app U s)) : f = g :=
  Scheme.Modules.hom_ext f g fun U => by
    ext s
    exact section_ext E' hE' fun hU => h U hU s

omit [IsIntegral X] in

lemma germ_app_eq_stalk (f : E ⟶ E') (U : X.Opens) (x : X) (hU : x ∈ U) (s : Γ(E, U)) :
    E'.presheaf.germ U x hU (f.app U s) =
      ((TopCat.Presheaf.stalkFunctor Ab x).map (Scheme.Modules.Hom.mapPresheaf f)).hom
        (E.presheaf.germ U x hU s) := by
  have := TopCat.Presheaf.stalkFunctor_map_germ_apply (F := E.presheaf) (G := E'.presheaf) U x hU
    (Scheme.Modules.Hom.mapPresheaf f) s
  exact this.symm

end BundlesAgree

open BundlesAgree in

theorem BundlesAgree.proof (h₁ : GenericGermInjective.Statement)
    (h₂ : HeightOneSections.Statement) : BundlesAgree.Statement := by
  intro X _ _ hN E E' hE hE' φ hφ
  have inj := h₁ X E hE
  have inj' := h₁ X E' hE'
  have mem : ∀ (F : X.Modules) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(F, U)) (x : X)
      (hx : x ∈ U), F.presheaf.germ U (genericPoint X) hU s ∈ genericImage F x :=
    fun F U hU s x hx => ⟨F.presheaf.germ U x hx s,
      TopCat.Presheaf.germ_stalkSpecializes_apply F.presheaf hx (genericPoint_specializes x) s⟩
  have hex : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)), ∃ t : Γ(E', U),
      E'.presheaf.germ U (genericPoint X) hU t = φ.toLinearMap (E.presheaf.germ U _ hU s) :=
    fun U hU s => h₂ X hN E' hE' U hU _ fun x hx hx1 => by
      rw [← hφ x hx1]
      exact AddSubgroup.mem_map.mpr ⟨_, mem E U hU s x hx, rfl⟩
  have hex' : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E', U)), ∃ t : Γ(E, U),
      E.presheaf.germ U (genericPoint X) hU t = φ.symm.toLinearMap (E'.presheaf.germ U _ hU s) :=
    fun U hU s => h₂ X hN E hE U hU _ fun x hx hx1 => by
      have h := mem E' U hU s x hx
      rw [← hφ x hx1] at h
      obtain ⟨a, ha, he⟩ := AddSubgroup.mem_map.mp h
      have : φ.symm (E'.presheaf.germ U (genericPoint X) hU s) = a := by
        rw [← he]
        exact φ.symm_apply_apply a
      exact this ▸ ha
  let f := homOfGeneric E E' φ.toLinearMap hex inj'
  let g := homOfGeneric E' E φ.symm.toLinearMap hex' inj
  have hf := germ_homOfGeneric_app E E' φ.toLinearMap hex inj'
  have hg := germ_homOfGeneric_app E' E φ.symm.toLinearMap hex' inj
  refine ⟨⟨f, g, ?_, ?_⟩, ?_, ?_⟩
  · refine hom_ext_of_germ E E inj fun U hU s => ?_
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, ConcreteCategory.comp_apply, hg,
      hf]
    simp
  · refine hom_ext_of_germ E' E' inj' fun U hU s => ?_
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, ConcreteCategory.comp_apply, hf,
      hg]
    simp
  · intro v
    obtain ⟨U, hU, s, rfl⟩ := E.presheaf.exists_germ_eq v
    rw [← germ_app_eq_stalk]
    exact hf U hU s
  · intro ψ hψ
    refine Iso.ext (hom_ext_of_germ E E' inj' fun U hU s => ?_)
    rw [germ_app_eq_stalk]
    exact (hψ _).trans (hf U hU s).symm

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PChartBundlesAgree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ChartBundlesAgree.lat_le (hHOI : HeightOneIntersection.Statement)
    {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] (B B' : ChartBundle o x r E) (i : τ) (hi : x i ≠ 0)
    (hN : IsNoetherianRing (chartRing o x i)) (hIC : IsIntegrallyClosed (chartRing o x i))
    (h1 : ∀ v ∈ B.lat i, ∃ s : chartRing o x i, s ≠ 0 ∧ (s : Ω) • v ∈ B'.lat i)
    (hq : ∀ q : Ideal (chartRing o x i), q.IsPrime → q.height = 1 → ∀ v : E,
      (∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B.lat i) →
        ∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B'.lat i) :
    B.lat i ≤ B'.lat i := by
  intro v hv
  let A := chartRing o x i
  let J : Ideal A :=
    { carrier := {a | (a : Ω) • v ∈ B'.lat i}
      add_mem' := fun {a b} ha hb => by
        change ((a + b : A) : Ω) • v ∈ B'.lat i
        rw [Subalgebra.coe_add, add_smul]
        exact add_mem ha hb
      zero_mem' := by
        change ((0 : A) : Ω) • v ∈ B'.lat i
        rw [Subalgebra.coe_zero, zero_smul]
        exact zero_mem _
      smul_mem' := fun c a ha => by
        change ((c * a : A) : Ω) • v ∈ B'.lat i
        rw [Subalgebra.coe_mul, mul_smul]
        exact B'.stable i c c.2 _ ha }
  have hJ : ∀ a : A, a ∈ J ↔ (a : Ω) • v ∈ B'.lat i := fun _ => Iff.rfl
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := B'.frame i hi
  have hfJ : ∀ l, (⟨f l, hf l⟩ : A) ∈ J.radical := by
    intro l
    obtain ⟨b, hli, hsp, hiff⟩ := hb l
    obtain ⟨n, hn⟩ : ∃ n : ℕ, f l ^ n • v ∈ B'.lat i := by
      by_cases hf0 : f l = 0
      · exact ⟨1, by rw [hf0, pow_one, zero_smul]; exact zero_mem _⟩
      · let bs := Module.Basis.mk hli (by rw [hsp])
        have hbs : ∀ q, bs q = b q := fun q => Module.Basis.mk_apply hli _ q
        let a := bs.equivFun v

        have coord : ∀ t : A, (t : Ω) • v ∈ B'.lat i →
            ∀ q, ∃ n : ℕ, f l ^ n * ((t : Ω) * a q) ∈ A := by
          intro t ht q
          obtain ⟨a', ha', he⟩ := (hiff ((t : Ω) • v)).1 ⟨0, by rw [pow_zero, one_smul]; exact ht⟩
          have e1 : bs.equivFun ((t : Ω) • v) = a' := by
            rw [he]
            simp_rw [← hbs]
            rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
          have e2 : a' q = (t : Ω) * a q := by
            rw [← e1, LinearEquiv.map_smul]
            rfl
          rw [← e2]
          exact ha' q
        refine (hiff v).2 ⟨a, fun q => ?_, ?_⟩
        · have hh : (⟨f l, hf l⟩ : A) ≠ 0 := fun e => hf0 (congrArg Subtype.val e)
          obtain ⟨m, g, hg⟩ := mem_away_of_heightOne hHOI A Ω Subtype.val_injective
            ⟨f l, hf l⟩ hh (a q)
            (by
              obtain ⟨s, hs0, hs⟩ := h1 v hv
              obtain ⟨n, hn⟩ := coord s hs q
              refine ⟨s, hs0, n, ⟨_, hn⟩, ?_⟩
              change f l ^ n * (s : Ω) * a q = f l ^ n * ((s : Ω) * a q)
              ring)
            (fun P hP hP1 _ => by
              have hv1 : ∃ s : A, s ∉ P ∧ (s : Ω) • v ∈ B.lat i :=
                ⟨1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h), by
                  rw [OneMemClass.coe_one, one_smul]; exact hv⟩
              obtain ⟨t, htP, ht⟩ := hq P hP hP1 v hv1
              obtain ⟨n, hn⟩ := coord t ht q
              refine ⟨t, htP, n, ⟨_, hn⟩, ?_⟩
              change f l ^ n * (t : Ω) * a q = f l ^ n * ((t : Ω) * a q)
              ring)
          refine ⟨m, ?_⟩
          have hg' : f l ^ m * a q = (g : Ω) := hg
          rw [hg']
          exact g.2
        · rw [← bs.sum_equivFun v]
          simp_rw [hbs]
          rfl
    exact ⟨n, (hJ _).2 (by rw [SubmonoidClass.coe_pow]; exact hn)⟩
  have h1J : (1 : A) ∈ J.radical := by
    have e : (1 : A) = ∑ l, (⟨c l, hc l⟩ : A) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      rw [OneMemClass.coe_one, ← hsum, AddSubmonoidClass.coe_finsetSum]
      rfl
    rw [e]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hfJ l)
  have hJtop : J = ⊤ := Ideal.radical_eq_top.1 ((Ideal.eq_top_iff_one _).2 h1J)
  have h1 : (1 : A) ∈ J := hJtop ▸ Submodule.mem_top
  have h1' := (hJ 1).1 h1
  rwa [OneMemClass.coe_one, one_smul] at h1'

theorem ChartBundlesAgree.proof (hHOI : HeightOneIntersection.Statement) :
    ChartBundlesAgree.Statement := by
  intro o _ Ω _ _ τ x r E _ _ B B' i hi hN hIC h1 h2 hq
  exact le_antisymm
    (ChartBundlesAgree.lat_le hHOI B B' i hi hN hIC h1 fun q hq' hq1 v => (hq q hq' hq1 v).1)
    (ChartBundlesAgree.lat_le hHOI B' B i hi hN hIC h2 fun q hq' hq1 v => (hq q hq' hq1 v).2)

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadIso
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

theorem SpreadIso.proof (h₁ : SpreadHom.Statement) (h₂ : SpreadHomInj.Statement) :
    SpreadIso.Statement := by
  intro X f _ _ a ha F G hF hG α
  obtain ⟨m₁, hm₁, H₁⟩ := h₁ X f a ha F G hF hG α.hom
  obtain ⟨m₂, hm₂, H₂⟩ := h₁ X f a ha G F hG hF α.inv
  obtain ⟨m₃, hm₃, I₃⟩ := h₂ X f a ha F F hF hF
  obtain ⟨m₄, hm₄, I₄⟩ := h₂ X f a ha G G hG hG
  obtain ⟨n, hn_def⟩ : ∃ n, n = m₁ * m₂ * m₃ * m₄ := ⟨_, rfl⟩
  have hn : 0 < n := by rw [hn_def]; positivity
  obtain ⟨ψ₁, e₁⟩ := H₁ n hn (Dvd.intro (m₂ * m₃ * m₄) (by rw [hn_def]; ring))
  obtain ⟨ψ₂, e₂⟩ := H₂ n hn (Dvd.intro (m₁ * m₃ * m₄) (by rw [hn_def]; ring))
  have k₁ : ψ₁ ≫ ψ₂ = 𝟙 _ := I₃ n hn (Dvd.intro (m₁ * m₂ * m₄) (by rw [hn_def]; ring)) _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₁, e₂, Iso.hom_inv_id])
  have k₂ : ψ₂ ≫ ψ₁ = 𝟙 _ := I₄ n hn (Dvd.intro (m₁ * m₂ * m₃) (by rw [hn_def]; ring)) _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₂, e₁, Iso.inv_hom_id])
  refine ⟨n, hn, ⟨ψ₁, ψ₂, k₁, k₂⟩, Iso.ext ?_⟩
  rw [pullbackIsoAlong_hom]
  exact e₁

end GroundTheory.Heights₂.Heights.Model
end

