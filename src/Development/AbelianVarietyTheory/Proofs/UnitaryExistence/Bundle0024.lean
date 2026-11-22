import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0003
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulMemOfMemSpan
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenusLatCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def toGen (Λ : Lat E n) : GenLat E n := ⟨Λ.L⟩

def IsLat (Λ : GenLat E n) : Prop := Λ.La.FG ∧ Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤

def latEquiv : Lat E n ≃ {Λ : GenLat E n // IsLat Λ} where
  toFun Λ := ⟨toGen Λ, Λ.fg, Λ.span_top⟩
  invFun Λ := ⟨Λ.1.La, Λ.2.1, Λ.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem stdLat_eq : stdLat E n = stdMod E n := rfl

theorem toGen_std : toGen (Lat.std E n) = ⟨stdLat E n⟩ := rfl

theorem ln_eq (Λ : Lat E n) : (toGen Λ).Ln = Λ.inter := inf_comm _ _

theorem span_smul_eq (N : ℕ) : Ideal.span {(N : 𝓞 E)} • stdLat E n = mulStd E n N :=
  Submodule.ideal_span_singleton_smul _ _

theorem levOK_iff (Λ : Lat E n) (N M : ℕ) : (toGen Λ).LevOK N M ↔ Λ.Admissible M N := by
  rw [GenLat.LevOK, Lat.Admissible, span_smul_eq, ln_eq]

theorem mIdx_eq (Λ : Lat E n) (N r : ℕ) : (toGen Λ).mIdx N r = Λ.cardCenterZero r N := by
  rw [GenLat.mIdx, Lat.cardCenterZero, span_smul_eq, ln_eq]; rfl

theorem zCard_eq (Λ : Lat E n) (N r : ℕ) : (toGen Λ).zCard N r = Λ.cardZ r N := by
  rw [GenLat.zCard, Lat.cardZ, span_smul_eq]; rfl

omit [NumberField E] in
theorem span_smul_le_iff (k : ℕ) (A B : Submodule (𝓞 E) (Fin n → E)) :
    Ideal.span {(k : 𝓞 E)} • A ≤ B ↔ ∀ x ∈ A, k • x ∈ B := by
  rw [Submodule.smul_le]
  constructor
  · intro h x hx
    have := h k (Ideal.mem_span_singleton_self _) x hx
    rwa [Nat.cast_smul_eq_nsmul] at this
  · intro h r hr x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    exact B.smul_mem _ (h x hx)

omit [NumberField E] in
theorem exists_uniform {p : ℕ} (hp : p.Prime) {A B : Submodule (𝓞 E) (Fin n → E)} (hA : A.FG)
    (h : ∀ x ∈ A, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ B) : ∃ k : ℕ, ¬ p ∣ k ∧ ∀ x ∈ A, k • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! k hk using h
  refine ⟨∏ s ∈ S, k s, ?_, ?_⟩
  · rw [Prime.dvd_finset_prod_iff hp.prime]
    rintro ⟨s, hs, hd⟩
    exact (hk s (Submodule.subset_span hs)).1 hd
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem s hs =>
      rw [← Finset.prod_erase_mul S k hs, mul_smul]
      exact B.toAddSubmonoid.nsmul_mem (hk s (Submodule.subset_span hs)).2 _
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact B.smul_mem _ hx

theorem eqAtPrime_of_trivAt (Λ : GenLat E n) {s : ℕ} (h : Λ.TrivAt s) (p : ℕ) (hp : p.Prime) (hs : p ∣ s) :
    EqAtPrime p Λ.La (stdMod E n) := by
  obtain ⟨k, hk, h1, h2⟩ := h
  have hpk : ¬ p ∣ k := fun hd => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hk hd hs)
  rw [span_smul_le_iff] at h1 h2
  exact ⟨fun x hx => ⟨k, hpk, h1 x hx⟩, fun x hx => ⟨k, hpk, h2 x hx⟩⟩

theorem trivAt_iff (Λ : Lat E n) (s : ℕ) : (toGen Λ).TrivAt s ↔ Λ.StdAt s := by
  refine ⟨fun h p hp hs => eqAtPrime_of_trivAt _ h p hp hs, fun h => ?_⟩
  let J : Ideal ℤ :=
    { carrier := {k | (∀ x ∈ Λ.L, k • x ∈ stdMod E n) ∧ ∀ x ∈ stdMod E n, k • x ∈ Λ.L}
      add_mem' := fun {a b} ha hb =>
        ⟨fun x hx => by rw [add_smul]; exact add_mem (ha.1 x hx) (hb.1 x hx),
          fun x hx => by rw [add_smul]; exact add_mem (ha.2 x hx) (hb.2 x hx)⟩
      zero_mem' := ⟨fun x _ => by simp, fun x _ => by simp⟩
      smul_mem' := fun c a ha =>
        ⟨fun x hx => by rw [smul_eq_mul, mul_smul]; exact zsmul_mem (ha.1 x hx) c,
          fun x hx => by rw [smul_eq_mul, mul_smul]; exact zsmul_mem (ha.2 x hx) c⟩ }
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal J).principal
  have hdJ : ((d.natAbs : ℕ) : ℤ) ∈ J := by
    rw [hd]
    exact Ideal.mem_span_singleton.2 (Int.dvd_natAbs.2 dvd_rfl)
  refine ⟨d.natAbs, Nat.coprime_of_dvd fun p hp hpd hps => ?_, ?_, ?_⟩
  · obtain ⟨k₁, hk₁, h₁⟩ := exists_uniform hp Λ.fg (h p hp hps).1
    obtain ⟨k₂, hk₂, h₂⟩ := exists_uniform hp (Lat.std E n).fg (h p hp hps).2
    have hJ : ((k₁ * k₂ : ℕ) : ℤ) ∈ J :=
      ⟨fun x hx => by rw [natCast_zsmul, mul_comm, mul_smul]; exact nsmul_mem (h₁ x hx) _,
        fun x hx => by rw [natCast_zsmul, mul_smul]; exact nsmul_mem (h₂ x hx) _⟩
    rw [hd] at hJ
    have h3 : d.natAbs ∣ k₁ * k₂ := Int.natCast_dvd_natCast.1 (Int.natAbs_dvd.2 (Ideal.mem_span_singleton.1 hJ))
    exact (hp.dvd_mul.1 (hpd.trans h3)).elim hk₁ hk₂
  · rw [span_smul_le_iff]
    intro x hx
    have := hdJ.1 x hx
    rwa [natCast_zsmul] at this
  · rw [span_smul_le_iff]
    intro x hx
    have := hdJ.2 x hx
    rwa [natCast_zsmul] at this

theorem fg_of_smul_mem {A : Submodule (𝓞 E) (Fin n → E)} {o : 𝓞 E} (ho : o ≠ 0)
    (h : ∀ x ∈ A, o • x ∈ stdMod E n) : A.FG := by
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 E) (Fin n → E) o) := by
    intro x y hxy
    funext j
    have := congrFun hxy j
    simp only [LinearMap.lsmul_apply, Pi.smul_apply, Algebra.smul_def] at this
    exact mul_left_cancel₀ (by simpa using ho) this
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  haveI : IsNoetherian (𝓞 E) (stdMod E n) := isNoetherian_of_fg_of_noetherian _ (Lat.std E n).fg
  refine Submodule.FG.of_le_of_isNoetherian (T := stdMod E n) ?_
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

variable [IsCMField E]

theorem conj_mem_range (z : E) :
    IsCMField.complexConj E z ∈ (algebraMap (𝓞 E) E).range ↔ ∃ a : 𝓞 E, (a : E) = z := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨IsCMField.ringOfIntegersComplexConj E a, ?_⟩
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    change IsCMField.complexConj E (algebraMap (𝓞 E) E a) = z
    rw [ha, IsCMField.complexConj_apply_apply]
  · rintro ⟨a, rfl⟩
    exact ⟨IsCMField.ringOfIntegersComplexConj E a, IsCMField.coe_ringOfIntegersComplexConj E a⟩

theorem conj_stdForm (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * w j = IsCMField.complexConj E (stdForm v w) := by
  simp [stdForm, map_sum]

theorem unimod_iff (Λ : Lat E n) : (toGen Λ).Unimod ↔ Λ.SelfDual := by
  simp only [GenLat.Unimod, Lat.SelfDual, conj_stdForm, conj_mem_range]
  rfl

theorem eq_zero_of_sum_conj (v : Fin n → E) (h : ∑ j, IsCMField.complexConj E (v j) * v j = 0) : v = 0 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := congrArg φ h
  simp only [map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_zero,
    Complex.conj_mul'] at h1
  have h2 : ∑ j, ‖φ (v j)‖ ^ 2 = 0 := by exact_mod_cast h1
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity] at h2
  funext j
  simpa using h2 j (Finset.mem_univ j)

omit [IsCMField E] in

private theorem exists_mul_mem_of_mem_span (A : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span E (A : Set (Fin n → E))) : ∃ o : 𝓞 E, o ≠ 0 ∧ o • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span ..)

private theorem span_eq_top_of_unimod (Λ : GenLat E n) (h : Λ.Unimod) :
    Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let v : Fin n → E := fun j => IsCMField.complexConj E (f (Pi.single j 1))
  have hpair : ∀ w : Fin n → E, ∑ j, IsCMField.complexConj E (v j) * w j = f w := by
    intro w
    conv_rhs => rw [pi_eq_sum_univ' w, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    simp only [v, IsCMField.complexConj_apply_apply]
  have hkill : ∀ w ∈ Λ.La, f w = 0 := fun w hw => hf (Submodule.subset_span hw)
  have hv : v ∈ Λ.La := (h v).2 fun w hw => by
    rw [hpair, hkill w hw]
    exact zero_mem _
  have hv0 : v = 0 := eq_zero_of_sum_conj v (by rw [hpair, hkill v hv])
  refine hf0 (LinearMap.ext fun w => ?_)
  rw [← hpair, hv0]
  simp

theorem isLat_of_unimod (Λ : GenLat E n) (h : Λ.Unimod) : IsLat Λ := by
  classical
  have hspan := span_eq_top_of_unimod Λ h
  refine ⟨?_, hspan⟩
  choose o ho0 ho using fun j : Fin n =>
    exists_mul_mem_of_mem_span Λ.La (x := Pi.single j 1) (hspan ▸ Submodule.mem_top)
  have hd : ∀ j, (∏ i, o i) • (Pi.single j 1 : Fin n → E) ∈ Λ.La := fun j => by
    rw [← Finset.prod_erase_mul _ o (Finset.mem_univ j), mul_smul]
    exact Λ.La.smul_mem _ (ho j)
  have hd0 : ∏ i, o i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ho0 i
  refine fg_of_smul_mem (o := IsCMField.ringOfIntegersComplexConj E (∏ i, o i))
    ((map_ne_zero_iff _ (IsCMField.ringOfIntegersComplexConj E).injective).2 hd0) fun x hx => ?_
  refine mem_stdMod.2 fun j => ?_
  obtain ⟨a, ha⟩ := (h _).1 (hd j) x hx
  refine ⟨a, Eq.trans ha ?_⟩
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
  rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, Algebra.smul_def, mul_one]
  congr 1

def selfDualEquiv : {Λ : Lat E n // Λ.SelfDual} ≃ {Λ : GenLat E n // Λ.Unimod} where
  toFun Λ := ⟨toGen Λ.1, (unimod_iff Λ.1).2 Λ.2⟩
  invFun Λ := ⟨latEquiv.symm ⟨Λ.1, isLat_of_unimod Λ.1 Λ.2⟩, (unimod_iff _).1 Λ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Poly

variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

theorem symO_eq (Λ : Lat E n) : symO (Dw := Dw) c (toGen Λ) = (symLat Dw c Λ).toSubring := by
  rw [symLat, Algebra.adjoin_eq_ring_closure, symO]
  rfl

theorem harmL_eq (Λ : Lat E n) (a : (E →+* ℂ) × ℕ → ℕ) :
    harmL (Dw := Dw) c (toGen Λ) a = harmLat Dw c a Λ := by
  ext P
  simp only [harmL, harmLat, symO_eq, Set.mem_setOf_eq]
  rfl

end Poly

end GlobalTheory.GenusLatCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.Frames.ChgBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem dualMap_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    (dualMap φ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp φ :=
  RingHom.ext fun a => by
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_eps {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) :=
  RingHom.ext fun x => by
    ext <;> simp [dualMap, epsMul, mul_comm]

theorem isCombAt_pull {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X}
    {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    {v' : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, v' j = spMap (dualMap φ) ≫ v j)
    {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} {w' : Sp (DualNumber T) ⟶ Xo.univ.t.G.left}
    (hw : w' = spMap (dualMap φ) ≫ w) (h : IsCombAt x v cf w) : IsCombAt x' v' (fun j => φ (cf j)) w' := by
  obtain ⟨u, hu, hprod⟩ := h
  let D : tEps x' ⟶ tEps x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap T (DualNumber T)) ≫ x'
    rw [hx, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, dualMap_alg])
  have hL : ∀ L : List (tEps x ⟶ Xo.univ.t.G), (L.map (D ≫ ·)).prod = D ≫ L.prod := by
    intro L
    induction L with
    | nil => simp [MonObj.comp_one]
    | cons a L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih, MonObj.comp_mul]
  refine ⟨fun j => D ≫ u j, fun j => ?_, ?_⟩
  · show spMap (dualMap φ) ≫ (u j).left = spMap (epsMul (φ (cf j))) ≫ v' j
    rw [hu j, hv j, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, dualMap_eps]
  · have e : (List.ofFn fun j => D ≫ u j) = (List.ofFn u).map (D ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [e, hL, Over.comp_left, hprod, hw]
    rfl

theorem isCombAt_unique {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v cf w) (h' : IsCombAt x v cf w') : w = w' := by
  obtain ⟨u, hu, hprod⟩ := h
  obtain ⟨u', hu', hprod'⟩ := h'
  have e : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [← hprod, ← hprod', e]

theorem ppx_le_cov {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem scal_pull {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i) (a : S) :
    (pm.appLE _ _ h).hom (scal x a i) = scal x' (φ a) i := by
  have key : ∀ (q : Gx x' ⟶ Sp S), q = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ →
      ∀ e : (PPx x').U i ≤ q ⁻¹ᵁ ⊤,
      q.appLE ⊤ ((PPx x').U i) e = (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appLE ⊤ _ (le_top) := by
    rintro q rfl e
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have M : (fst (Over.mk x) Xo.univ.t.G).left.appTop ≫ (Gx x).presheaf.map (homOfLE le_top).op ≫ pm.appLE _ _ h =
      (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appTop ≫ (Gx x').presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.map_appLE]
    have e1 : (fst (Over.mk x) Xo.univ.t.G).left.appTop =
        (fst (Over.mk x) Xo.univ.t.G).left.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app _).symm
    rw [e1]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((key _ hf _).trans rfl)
  have M' := congrArg (fun f => f.hom (toΓ S a)) M
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at M'
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  show (pm.appLE _ _ h).hom (((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a))) =
    ((Gx x').presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x') Xo.univ.t.G).left.appTop.hom (toΓ T (φ a)))
  rw [M']
  congr 2
  exact N.symm

theorem can_exists {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap φ ≫ x) :
    ∃ pm : Gx x' ⟶ Gx x, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ := by
  let pm : Gx x' ⟶ Gx x :=
    pullback.lift (pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ)
      (pullback.snd (Over.mk x').hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ ≫ x =
          pullback.snd (Over.mk x').hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hx]
        exact pullback.condition)
  exact ⟨pm, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem gx_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {Z : Scheme.{0}} {p q : Z ⟶ Gx x}
    (hs : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left) : p = q :=
  pullback.hom_ext (f := (Over.mk x).hom) (g := Xo.univ.t.G.hom) hf hs

theorem square {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) {y y' : Sp S ⟶ Xo.X}
    {z z' : Sp T ⟶ Xo.X} (pmA : Gx z ⟶ Gx y) (pmB : Gx z' ⟶ Gx y') (pmC : Gx y' ⟶ Gx y) (pm : Gx z' ⟶ Gx z)
    (hsA : pmA ≫ (snd (Over.mk y) Xo.univ.t.G).left = (snd (Over.mk z) Xo.univ.t.G).left)
    (hfA : pmA ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk z) Xo.univ.t.G).left ≫ spMap φ)
    (hsB : pmB ≫ (snd (Over.mk y') Xo.univ.t.G).left = (snd (Over.mk z') Xo.univ.t.G).left)
    (hfB : pmB ≫ (fst (Over.mk y') Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left ≫ spMap φ)
    (hsC : pmC ≫ (snd (Over.mk y) Xo.univ.t.G).left = (snd (Over.mk y') Xo.univ.t.G).left)
    (hfC : pmC ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y') Xo.univ.t.G).left ≫ spMap (RingHom.id S))
    (hs : pm ≫ (snd (Over.mk z) Xo.univ.t.G).left = (snd (Over.mk z') Xo.univ.t.G).left)
    (hf : pm ≫ (fst (Over.mk z) Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left ≫ spMap (RingHom.id T))
    (sy : LB.Sec (PPx y)) (sy' : LB.Sec (PPx y')) (sz : LB.Sec (PPx z))
    (haA : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z).U i ≤ pmA ⁻¹ᵁ (PPx y).U i),
      (pmA.appLE _ _ h).hom (sy.f i) = sz.f i)
    (haC : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y').U i ≤ pmC ⁻¹ᵁ (PPx y).U i),
      (pmC.appLE _ _ h).hom (scal y a i * sy.f i) = sy'.f i)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z').U i ≤ pm ⁻¹ᵁ (PPx z).U i)
    (hB : (PPx z').U i ≤ pmB ⁻¹ᵁ (PPx y').U i) :
    (pm.appLE _ _ h).hom (scal z (φ a) i * sz.f i) = (pmB.appLE _ _ hB).hom (sy'.f i) := by
  rw [spMap_id] at hfC hf
  replace hfC : pmC ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y') Xo.univ.t.G).left :=
    hfC.trans (Category.comp_id _)
  replace hf : pm ≫ (fst (Over.mk z) Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left :=
    hf.trans (Category.comp_id _)
  have hcomp : pm ≫ pmA = pmB ≫ pmC := by
    apply gx_ext
    · rw [Category.assoc, hsA, hs, Category.assoc, hsC, hsB]
    · rw [Category.assoc, hfA, Category.assoc, hfC]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap φ) hf)).trans hfB.symm
  have hA := ppx_le_cov pmA hsA i
  have hC := ppx_le_cov pmC hsC i
  have key : ∀ (q : Gx z' ⟶ Gx y), q = pmB ≫ pmC → ∀ hh : (PPx z').U i ≤ q ⁻¹ᵁ (PPx y).U i,
      (q.appLE _ _ hh).hom (scal y a i * sy.f i) = (pmB.appLE _ _ hB).hom (sy'.f i) := by
    rintro q rfl hh
    have e : (pmB ≫ pmC).appLE _ _ hh = pmC.appLE _ _ hC ≫ pmB.appLE _ _ hB :=
      (Scheme.Hom.appLE_comp_appLE pmB pmC _ _ _ hC hB).symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, haC i hC]
  rw [← haA i hA, ← scal_pull φ pmA hfA i hA, ← map_mul (pmA.appLE _ _ hA).hom]
  have e2 := congrArg (fun f => f.hom (scal y a i * sy.f i))
    (Scheme.Hom.appLE_comp_appLE pm pmA _ _ _ hA h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2]
  exact key _ hcomp _

theorem frChg_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T) (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : S), FrChg g a y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ a) z z') := by
  intro E _ _ _ H Dw l Xo c S _ _ T _ _ φ y y' z z' g a hb hz
  obtain ⟨hx, hcomb, pmC, hsC, hfC, haC⟩ := hb
  obtain ⟨hx1, hu1, pmA, hsA, hfA, haA⟩ := hz
  constructor
  · rintro ⟨hx2, hu2, pmB, hsB, hfB, haB⟩
    have hxz : z'.x = z.x := by rw [hx2, hx1, hx]
    refine ⟨hxz, fun τ i => isCombAt_pull φ.toRingHom hx1 (hu1 τ) (hu2 τ i) (hcomb τ i), ?_⟩
    obtain ⟨pm, hs, hf⟩ := can_exists (RingHom.id T) (x := z.x) (x' := z'.x)
      (by rw [spMap_id, Category.id_comp, hxz])
    refine ⟨pm, hs, hf, fun i h => ?_⟩
    have hB := ppx_le_cov pmB hsB i
    exact (square φ.toRingHom a pmA pmB pmC pm hsA hfA hsB hfB hsC hfC hs hf y.s y'.s z.s haA haC i h hB).trans
      (haB i hB)
  · rintro ⟨hxz, hc2, pm, hs, hf, ha⟩
    have hx2 : z'.x = spMap φ.toRingHom ≫ y'.x := by rw [hxz, hx1, hx]
    refine ⟨hx2, fun τ i => isCombAt_unique (hc2 τ i)
      (isCombAt_pull φ.toRingHom hx1 (hu1 τ) rfl (hcomb τ i)), ?_⟩
    obtain ⟨pmB, hsB, hfB⟩ := can_exists φ.toRingHom hx2
    refine ⟨pmB, hsB, hfB, fun i hB => ?_⟩
    have h := ppx_le_cov pm hs i
    exact (square φ.toRingHom a pmA pmB pmC pm hsA hfA hsB hfB hsC hfC hs hf y.s y'.s z.s haA haC i h hB).symm.trans
      (ha i h)

end GlobalTheory.Frames.ChgBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModelBaseTrivModels
section
noncomputable section

namespace GlobalTheory.PeriodRowsCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem isTypeFn_letters (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  classical
  have hinj : Function.Injective (relab c σ) := by
    intro τ₁ τ₂ h
    ext a
    have := congrArg (fun f : E →+* ℂ => f a) h
    exact congrArg Subtype.val (σ.injective this)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := fun τ => by
    have hval : relab c σ τ (H.rt : E) = σ ⟨τ (H.rt : E), c.conj τ _⟩ := rfl
    rw [hval]
    refine ⟨fun h => congrArg Subtype.val (σ.injective (h.trans hσ0.symm)), fun h => ?_⟩
    exact (congrArg σ (Subtype.ext h)).trans hσ0
  intro τ
  obtain ⟨τ₀, rfl⟩ := Finite.injective_iff_surjective.1 hinj τ
  have hcard : Nat.card {i // relab c σ (e i).1 = relab c σ τ₀} = Dw.mult τ₀ := by
    have e1 : {i // relab c σ (e i).1 = relab c σ τ₀} ≃ {i // (e i).1 = τ₀} :=
      Equiv.subtypeEquivRight (fun i => hinj.eq_iff)
    have e2 : {i // (e i).1 = τ₀} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    rw [Nat.card_congr (e1.trans (e2.trans (Equiv.sigmaSubtype τ₀))), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]
    exact if_pos ((hrel τ₀).1 h)
  · rw [hcard]
    exact if_neg (fun h' => h ((hrel τ₀).2 h'))

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)} {F : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.FamAt Xo c σ e} {r : ℕ}

def modelsEquiv (F : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.FamAt Xo c σ e) (r : ℕ) :
    Rows.ModelsOf F r ≃ GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.ModelsOf F r where
  toFun M := ⟨M.X, M.φ⟩
  invFun M := ⟨M.X, M.φ⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem modelsEquiv_φ (M : Rows.ModelsOf F r) : (modelsEquiv F r M).φ = M.φ := rfl

def trivChar (X : Data E r) : Data E r :=
  { X with
    χ := fun _ _ => 1
    χ_mul := fun _ _ _ _ _ => (one_mul 1).symm
    χ_add := fun _ _ _ _ => (one_mul 1).symm
    χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow 1⟩ }

def trivModels (M : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.ModelsOf F r) : Rows.ModelsOf F r :=
  ⟨fun k => trivChar (M.X k), M.φ⟩

end GlobalTheory.PeriodRowsCompare
end
end

