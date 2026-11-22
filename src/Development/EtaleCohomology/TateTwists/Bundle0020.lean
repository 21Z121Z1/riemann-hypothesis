import Development.EtaleCohomology.TateTwists.Bundle0007
import Development.EtaleCohomology.TateTwists.Bundle0001
import Development.EtaleCohomology.TateTwists.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.TateTwists.Bundle0012
import Development.EtaleCohomology.TateTwists.Bundle0011
import Development.EtaleCohomology.TateTwists.StrictHenselianAcyclic
import Development.EtaleCohomology.TateTwists.Bundle0010

-- bundled from Development.EtaleCohomology.TateTwists.TAwAssoc0Of
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma aw_diag {M : Type*} [AddCommMonoid M] (N : ℕ) (Φ : ℕ → ℕ → M) :
    ∑ q ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (q + 1), Φ p (q - p) =
      ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), Φ p r := by
  rw [Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_range] at hp
  rw [show N + 1 - p = N - p + 1 by omega]

lemma bil_zsmul_left {S A B C : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup C] [Module S C] (f : A →ₗ[S] B →ₗ[S] C) (c : ℤ) (a : A) (b : B) :
    f (c • a) b = c • f a b := by
  have := map_zsmul (f.flip b) c a
  simpa using this

lemma bil_sum_left {S A B C ι : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup C] [Module S C] (f : A →ₗ[S] B →ₗ[S] C) (s : Finset ι) (a : ι → A) (b : B) :
    f (∑ i ∈ s, a i) b = ∑ i ∈ s, f (a i) b := by
  have := map_sum (f.flip b) a s
  simpa using this

variable {R : Type} [CommRing R]

lemma mul_ev_right {A B C : Cx R} (P : Pair A B C) {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) {s k w : ℤ}
    (a : Sec (A.X s) U) (γ : Cochain ((chains R).obj E) B k) (t t' j j' : ℕ) (ht : t = t') (hj : j = j')
    (h : s + (-(t : ℤ) + k) = w) (h' : s + (-(t' : ℤ) + k) = w) (hl : j + t ≤ N) (hl' : j' + t' ≤ N) :
    P.mul U s (-(t : ℤ) + k) w h a (ev γ t _ rfl U (x.sub j t hl)) =
      P.mul U s (-(t' : ℤ) + k) w h' a (ev γ t' _ rfl U (x.sub j' t' hl')) := by
  subst ht hj; rfl

theorem t_aw_assoc0_of (hev : EtaleCochainEvaluationLinear) (hsub : EtaleSimplexSubfaceComposition) : t_aw_assoc0 := by
  intro R _ I J K M M' L μ ν μ' ν' hass E n m k nm mk w h1 h2 h3 h4 α β γ ab bc x y hab hx hbc hy
  refine (hev R).2.2.1 x y fun N s hs U z => ?_
  rw [hx N s hs U z, hy N s hs U z]
  let Φ : ℕ → ℕ → Sec (L.X s) U := fun p r => if h : p + r ≤ N then
    (((m * (p : ℤ) + k * ((p : ℤ) + r)).negOnePow : ℤˣ) : ℤ) •
      ν'.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + mk) s (by omega) (ev α p _ rfl U (z.sub 0 p (by omega)))
        (μ'.mul U (-(r : ℤ) + m) (-((N - p - r : ℕ) : ℤ) + k) (-((N - p : ℕ) : ℤ) + mk) (by omega)
          (ev β r _ rfl U (z.sub p r (by omega))) (ev γ (N - p - r) _ rfl U (z.sub (p + r) (N - p - r) (by omega))))
    else 0
  have hsg : ∀ a b c : ℤ, a + b = c → ((a.negOnePow : ℤˣ) : ℤ) * ((b.negOnePow : ℤˣ) : ℤ) = ((c.negOnePow : ℤˣ) : ℤ) := by
    intro a b c h; rw [← Units.val_mul, ← Int.negOnePow_add, h]
  calc _ = ∑ q : Fin (N + 1), ∑ p : Fin ((q : ℕ) + 1), Φ p ((q : ℕ) - p) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hab, bil_sum_left, Finset.smul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          have hp := p.is_lt
          have hq := q.is_lt
          simp only [Φ]
          rw [dif_pos (by omega), Units.smul_def, Units.smul_def, bil_zsmul_left, smul_smul,
            hsg _ _ (m * ((p : ℕ) : ℤ) + k * (((p : ℕ) : ℤ) + (((q : ℕ) - (p : ℕ) : ℕ) : ℤ)))
              (by push_cast [Nat.cast_sub (show (p : ℕ) ≤ q by omega)]; ring)]
          congr 1
          rw [hass U _ _ _ _ (-((N - p : ℕ) : ℤ) + mk) s _ _ (by omega) (by omega)]
          rw [(hsub z).1 0 q 0 p, (hsub z).1 0 q p (q - p)]
          simp only [Nat.zero_add]
          congr 1
          exact mul_ev_right _ z _ γ (N - q) (N - p - (q - p)) q (p + (q - p)) (by omega) (by omega) _ _ _ _
    _ = ∑ q ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (q + 1), Φ p (q - p) := by
          rw [← Fin.sum_univ_eq_sum_range (fun q => ∑ p ∈ Finset.range (q + 1), Φ p (q - p))]
          exact Finset.sum_congr rfl fun q _ => Fin.sum_univ_eq_sum_range (fun p => Φ p (q - p)) _
    _ = ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), Φ p r := aw_diag N Φ
    _ = ∑ p : Fin (N + 1), ∑ r : Fin (N - (p : ℕ) + 1), Φ p r := by
          rw [← Fin.sum_univ_eq_sum_range (fun p => ∑ r ∈ Finset.range (N - p + 1), Φ p r)]
          exact Finset.sum_congr rfl fun p _ => (Fin.sum_univ_eq_sum_range (fun r => Φ p r) _).symm
    _ = _ := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hbc, map_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hp := p.is_lt
          have hr := r.is_lt
          simp only [Φ]
          rw [dif_pos (by omega), Units.smul_def, Units.smul_def, map_zsmul, smul_smul,
            hsg _ _ (m * ((p : ℕ) : ℤ) + k * (((p : ℕ) : ℤ) + ((r : ℕ) : ℤ))) (by subst h3; ring)]
          rw [(hsub z).1 p (N - p) 0 r, (hsub z).1 p (N - p) r (N - p - r)]
          simp only [Nat.add_zero]

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TTwpairExPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleTateTwistCupPairingExistsAndCupUnique : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
      ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h

theorem t_twpair_ex_of (htw : EtaleTateTwistCupPairingExistsAndCupUnique) : t_twpair_ex := by
  intro q _ i j
  exact ⟨twPair q i j, (htw q i j).1⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TtResSidePf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tensor_universal_property : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u

def tensor_quasi_isomorphism : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u

theorem tt_res_side_of (huniv : tensor_universal_property) (hqis : tensor_quasi_isomorphism) : tt_res_side := by
  intro q _ i I J M T e hI hJ hflat σ τ hσ hτ
  obtain ⟨hIge, ε, hε, hgen⟩ := hI
  obtain ⟨u, hu, -⟩ := (huniv (ZMod q) σ hσ).1 τ ε (𝟙 J)
  have := hIge
  have := hJ
  refine ⟨u, hqis (ZMod q) σ τ hσ hτ hflat ε u hu, fun U ζ b => ?_⟩
  rw [hu U 0 0 0 (add_zero 0), hgen U ζ]
  simp only [HomologicalComplex.id_f]
  rfl

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TtTensExPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

structure TensPre {R : Type} [CommRing R] (I J : Cx R) where
  P : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ
  e : ∀ (U : Scheme.{0}) (w : ℤ), Tens I J U w ≃ₗ[ULift.{1} R] (P.X w).obj (op U)
  nat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w),
    e V w (Tens.res g w x) = ((P.X w).map g.op).hom (e U w x)
  leibniz : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    ((P.d w (w + 1)).app (op U)).hom (e U w (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))) =
      e U (w + 1) (DirectSum.of _ ⟨(s + 1, t), by omega⟩ (Sec.map (I.d s (s + 1)) a ⊗ₜ b)) +
      s.negOnePow • e U (w + 1) (DirectSum.of _ ⟨(s, t + 1), by omega⟩ (a ⊗ₜ Sec.map (J.d t (t + 1)) b))

def tt_tens_pre : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), Nonempty (TensPre I J)

def tt_tens_sheafify : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), TensPre I J → ∃ (K : Cx R) (μ : Pair I J K), μ.IsTensor

theorem tt_tens_ex_of (hpre : tt_tens_pre) (hsh : tt_tens_sheafify) : tt_tens_ex := by
  intro R _ I J
  obtain ⟨T⟩ := hpre R I J
  exact hsh R I J T

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TtTensGePf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tens_univ_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0)

theorem tt_tens_ge_of (h : tens_univ_ge) : tt_tens_ge := by
  intro R _ I J K μ hI hJ hμ
  exact h R μ hμ hI hJ

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TtTwistSidePf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.TwSide

def tw_mul : Prop := ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ)

def tw_flat : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i)

def flip_ex : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧ (μ.IsTensor → ν.IsTensor)

def tens_qis : Prop := ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u

variable {R : Type} [CommRing R]

theorem sec_sub {F : Shv R} (h : IsZero F) (U : Scheme.{0}) : Subsingleton (Sec F U) := by
  constructor; intro a b
  have : 𝟙 F = 0 := h.eq_of_src _ _
  have ha : a = Sec.map (𝟙 F) a := rfl
  have hb : b = Sec.map (𝟙 F) b := rfl
  rw [ha, hb, this]; rfl

theorem flat_zero {F : Shv R} (h : IsZero F) : FlatS F := by
  refine ⟨F.obj, 𝟙 _, fun U y => LateralTheory.EtaleFoundations.TensFam.loc_top fun V g => ⟨Sec.res g y, rfl⟩,
    fun U x _ => LateralTheory.EtaleFoundations.TensFam.loc_top fun V g => @Subsingleton.elim _ (sec_sub h V) _ _, fun U _ => ?_⟩
  haveI := sec_sub h U
  infer_instance

open ZeroObject in
theorem flat_sgl {F : Shv R} (hF : FlatS F) (t : ℤ) : FlatS ((sgl F).X t) := by
  by_cases ht : t = 0
  · subst ht
    exact (show FlatS (if (0:ℤ) = 0 then F else 0) by rw [if_pos rfl]; exact hF)
  · exact flat_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht)

theorem sgl_sub (F : Shv R) {t : ℤ} (ht : t ≠ 0) (U : Scheme.{0}) : Subsingleton (Sec ((sgl F).X t) U) :=
  sec_sub (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht) U

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)).symm

theorem map_comp' {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem map_zero' {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem tens_ind {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (P : Tens I J U w → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (ht : ∀ p a b, P (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b))) (x : Tens I J U w) : P x := by
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | add x y hx hy => exact hadd _ _ hx hy
  | of p z =>
    induction z using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => simpa [DirectSum.lof_eq_of] using ht p a b
    | add z1 z2 h1 h2 => rw [map_add]; exact hadd _ _ h1 h2

theorem lift_lof {I J K : Cx R} (τ : Pair I J K) (U : Scheme.{0}) (w : ℤ) p a b :
    τ.lift U w (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b)) = τ.mul U p.1.1 p.1.2 w p.2 a b := by
  simp [Pair.lift, DirectSum.toModule_lof]

theorem shv_isZero {F : Shv R} (h : ∀ U : Scheme.{0}, ∀ y : Sec F U, y = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U y
  exact h _ y

end LateralTheory.EtaleFoundations.TwSide

namespace LateralTheory.EtaleFoundations.TwSide
variable {q : ℕ} [NeZero q]

noncomputable def T {A B J : Cx (ZMod q)} (ε : B ⟶ J) (U : Scheme.{0}) (w : ℤ) :
    Tens A B U w →ₗ[ULift.{1} (ZMod q)] Tens A J U w :=
  DirectSum.toModule _ _ _ fun p => (DirectSum.lof (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = w}
      (fun p => Sec (A.X p.1.1) U ⊗[ULift.{1} (ZMod q)] Sec (J.X p.1.2) U) p).comp
    (TensorProduct.map LinearMap.id ((ε.f p.1.2).hom.app (op U)).hom)

theorem T_lof {A B J : Cx (ZMod q)} (ε : B ⟶ J) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (A.X p.1.1) U) (b : Sec (B.X p.1.2) U) :
    T ε U w (DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ Sec.map (ε.f p.1.2) b) := by
  simp [T, DirectSum.toModule_lof]

theorem smul_eq (c : ULift.{1} (ZMod q)) : c = ((c.down.val : ℕ) : ULift.{1} (ZMod q)) := by
  apply ULift.ext; rw [ULift.down_natCast, ZMod.natCast_zmod_val]

noncomputable def ofFam {F G : Shv (ZMod q)} (φ : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom
        { toFun := φ U.unop
          map_add' := map_add _
          map_smul' := fun c y => by
            rw [smul_eq c]
            simp only [Nat.cast_smul_eq_nsmul, map_nsmul, RingHom.id_apply] }
      naturality := fun U V g => by
        ext y
        exact (hφ V.unop U.unop g.unop y).symm }

theorem twist_side (htm : tw_mul) (htf : tw_flat) (hfl : flip_ex) (hqis : tens_qis) (i j k : ℤ) (hk : i + j = k)
    {J M : Cx (ZMod q)} (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U) (hJ : IsTwRes q j J e')
    (hflat : ∀ t, FlatS (J.X t)) (σ : Pair (sgl (tw q i)) J M) (hσ : σ.IsTensor) :
    IsTwRes q k M fun U ζ => σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) (e' U ζ) := by
  obtain ⟨μ, hμ, hgen⟩ := htm q i j k hk
  obtain ⟨hJge, ε', hε', hε'gen⟩ := hJ

  have hMge : M.IsStrictlyGE 0 := by
    refine (CochainComplex.isStrictlyGE_iff M 0).2 fun w hw => shv_isZero fun U y => ?_
    apply LateralTheory.EtaleFoundations.TensFam.sep
    obtain ⟨S, hS, h1⟩ := hσ.1 U w y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := h1 V g hg
    rw [← hx, show Sec.res g (0 : Sec (M.X w) U) = 0 from map_zero _]
    refine tens_ind (fun x => σ.lift V w x = 0) (map_zero _) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
      (fun p a b => ?_) x
    rw [lift_lof]
    rcases p with ⟨⟨s, t⟩, hst⟩
    by_cases hs : s = 0
    · have ht : t < 0 := by simp only at hst; omega
      haveI := sec_sub (CochainComplex.isZero_of_isStrictlyGE J 0 t (by omega)) V
      rw [Subsingleton.elim b 0, map_zero]
    · haveI := sgl_sub (tw q i) hs V
      rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
  let b : ∀ U : Scheme.{0}, Tens (sgl (tw q i)) (sgl (tw q j)) U 0 →+ Sec (M.X 0) U :=
    fun U => ((σ.lift U 0).comp (T ε' U 0)).toAddMonoidHom
  have hbv : ∀ U p a c, b U (DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ c)) =
      σ.mul U p.1.1 p.1.2 0 p.2 a (Sec.map (ε'.f p.1.2) c) := by
    intro U p a c
    simp only [b, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, T_lof, lift_lof]
  have hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g 0 x) := by
    intro V U g x
    refine tens_ind (fun x => Sec.res g (b U x) = b V (Tens.res g 0 x)) (by simp)
      (fun x y hx hy => by simp only [map_add, hx, hy]) (fun p a c => ?_) x
    rw [hbv, σ.nat, map_res]
    simp only [Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul]
    rw [hbv]
  obtain ⟨φ, hφnat, hφlift⟩ := LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing (ZMod q) (ZMod q) μ hμ 0 (M.X 0) b hb
  have hd : ∀ U (y : Sec ((sgl (tw q k)).X 0) U), Sec.map (M.d 0 (0 + 1)) (φ U y) = 0 := by
    intro U y
    apply LateralTheory.EtaleFoundations.TensFam.sep
    obtain ⟨S, hS, h1⟩ := hμ.1 U 0 y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := h1 V g hg
    rw [show Sec.res g (0 : Sec (M.X (0 + 1)) U) = 0 from map_zero _, map_res, hφnat, ← hx, hφlift]
    refine tens_ind (fun x => Sec.map (M.d 0 (0 + 1)) (b V x) = 0) (by simp)
      (fun x y hx hy => by simp only [map_add, hx, hy, add_zero]) (fun p a c => ?_) x
    rcases p with ⟨⟨s, t⟩, hst⟩
    rw [hbv]
    have hl := σ.leibniz V s t 0 hst a (Sec.map (ε'.f t) c)
    have hz : ∀ (F : Shv (ZMod q)) (m n : ℤ), (sgl F).d m n = 0 := fun F m n => HomologicalComplex.single_obj_d _ _ _ _ _
    rw [hl, ← map_comp', ε'.comm, map_comp', hz, hz]
    simp only [map_zero', map_zero, LinearMap.zero_apply, smul_zero, add_zero]
  let u : sgl (tw q k) ⟶ M := HomologicalComplex.mkHomFromSingle (sglι (tw q k) ≫ ofFam φ hφnat) (by
    intro l hl
    obtain rfl : l = 0 + 1 := by simp at hl; omega
    ext U y
    exact hd _ _)
  have hu0 : ∀ U (z : Sec ((sgl (tw q k)).X 0) U), Sec.map (u.f 0) z = φ U z := by
    intro U z
    rw [HomologicalComplex.mkHomFromSingle_f, ← Category.assoc]
    show Sec.map (ofFam φ hφnat) (Sec.map ((HomologicalComplex.singleObjXSelf _ 0 (tw q k)).hom ≫ (HomologicalComplex.singleObjXSelf _ 0 (tw q k)).inv) z) = _
    rw [Iso.hom_inv_id]; rfl
  have cmp : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q i)).X s) U) (c : Sec ((sgl (tw q j)).X t) U),
      Sec.map (u.f w) (μ.mul U s t w h a c) = σ.mul U s t w h a (Sec.map (ε'.f t) c) := by
    intro U s t w h a c
    by_cases hs : s = 0
    · by_cases ht : t = 0
      · subst hs ht
        obtain rfl : w = 0 := by omega
        rw [hu0]
        have := hφlift U (DirectSum.lof (ULift.{1} (ZMod q)) _ _ ⟨(0,0), h⟩ (a ⊗ₜ c))
        rw [lift_lof] at this
        rw [this, hbv]
      · haveI := sgl_sub (tw q j) ht U
        rw [Subsingleton.elim c 0]
        simp only [map_zero]
    · haveI := sgl_sub (tw q i) hs U
      rw [Subsingleton.elim a 0]
      simp only [map_zero, LinearMap.zero_apply]
  obtain ⟨μf, hμf, -, hμfT⟩ := hfl (ZMod q) μ
  obtain ⟨σf, hσf, -, hσfT⟩ := hfl (ZMod q) σ
  haveI := hJge
  haveI := hε'
  have hcomp : μf.Compat σf ε' (𝟙 _) u := by
    intro U s t w h a c
    rw [HomologicalComplex.id_f]
    show _ = σf.mul U s t w h (Sec.map (ε'.f s) a) c
    rw [hμf U t s w (by omega) c a, hσf U t s w (by omega) c _, Units.smul_def, Units.smul_def, ← cmp]
    exact map_zsmul ((u.f w).hom.app (op U)).hom _ _
  have hu : QuasiIso u := hqis (ZMod q) μf σf (hμfT hμ) (hσfT hσ) (flat_sgl (htf q i)) ε' u hcomp
  refine ⟨hMge, u, hu, fun U ζ => ?_⟩
  rw [← hgen U ζ, cmp, hε'gen]

end LateralTheory.EtaleFoundations.TwSide

theorem LateralTheory.EtaleFoundations.tt_twist_side_of (htm : LateralTheory.EtaleFoundations.TwSide.tw_mul) (htf : LateralTheory.EtaleFoundations.TwSide.tw_flat)
    (hfl : LateralTheory.EtaleFoundations.TwSide.flip_ex) (hqis : LateralTheory.EtaleFoundations.TwSide.tens_qis) : LateralTheory.EtaleFoundations.tt_twist_side := by
  intro q _ i j k hk J M e' hJ hflat σ hσ
  exact LateralTheory.EtaleFoundations.TwSide.twist_side htm htf hfl hqis i j k hk e' hJ hflat σ hσ
end

-- bundled from Development.EtaleCohomology.TateTwists.TwLocPfR
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwLocPf

theorem ofRings_sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}}
    (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := congrArg (fun f => f.hom x)
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  exact h.symm

theorem twGen_res (q : ℕ) (i : ℤ) (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  refine (ofRings_sec_res (twF q i) g _).trans ?_
  unfold twGen
  congr 1
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]

def TwSecLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
  Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)

def TwTors : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ),
  c • twGen i ζ = 0 → q ∣ c

theorem TwLoc_of (h1 : TwSecLoc) (h2 : TwTors) : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc := by
  intro q _ i
  exact ⟨fun U ζ y => h1 q i U ζ y, fun U _ ζ c hc => h2 q i U ζ c hc, fun V U g ζ => twGen_res q i V U g ζ⟩

end LateralTheory.EtaleFoundations.TwLocPf
end
end

-- bundled from Development.EtaleCohomology.TateTwists.TwpairZcFunPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

section
variable {R : Type} [CommRing R]

lemma zc_pull_mk {K L I : Cx R} (f : K ⟶ L) (n : ℤ) (b : Cocycle L I n) :
    cpull f I n (CohomologyClass.mk b) =
      CohomologyClass.mk (Cocycle.mk ((Cochain.ofHom f).comp b.1 (zero_add n)) (n + 1) rfl
        (by rw [δ_ofHom_comp, Cocycle.δ_eq_zero, Cochain.comp_zero])) := by
  rw [cpre_mk]; congr 1

lemma zc_push_mk {K I J : Cx R} (g : I ⟶ J) (n : ℤ) (a : Cocycle K I n) :
    cpush K g n (CohomologyClass.mk a) =
      CohomologyClass.mk (Cocycle.mk (a.1.comp (Cochain.ofHom g) (add_zero n)) (n + 1) rfl
        (by rw [δ_comp_ofHom, Cocycle.δ_eq_zero, Cochain.zero_comp])) := by
  rw [cpost_mk]; congr 1

end

theorem twpair_zc_fun_of : twpair_zc_fun := by
  intro R _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K I n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    constructor
    · rw [zc_pull_mk]; congr 1; apply Cocycle.ext; simp [Cochain.id_comp]
    · rw [zc_push_mk]; congr 1; apply Cocycle.ext; simp [Cochain.comp_id]
  · intro K L M f g I n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_pull_mk, zc_pull_mk, zc_pull_mk]; congr 1; apply Cocycle.ext
    simp [Cochain.ofHom_comp]
  · intro K I J M f g n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_push_mk, zc_push_mk, zc_push_mk]
    congr 1
  · intro K L I J f g n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_push_mk, zc_pull_mk, zc_pull_mk, zc_push_mk]; congr 1; apply Cocycle.ext
    simp
  · intro K L f g ⟨ho⟩ I n
    obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g ho
    constructor
    · ext x
      obtain ⟨b, rfl⟩ := x.mk_surjective
      rw [zc_pull_mk, zc_pull_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨n.negOnePow • z.comp b.1 (by omega), ?_⟩
      have hb : δ n (n + 1) (b : Cochain L I n) = 0 := Cocycle.δ_eq_zero _ _
      have hz' : δ (-1) 0 z = Cochain.ofHom f - Cochain.ofHom g := by rw [hz]; abel
      rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) rfl]
      simp only [hb, Cochain.comp_zero, zero_add, smul_smul, Int.units_mul_self, one_smul, hz',
        Cochain.sub_comp]
      rfl
    · ext x
      obtain ⟨a, rfl⟩ := x.mk_surjective
      rw [zc_push_mk, zc_push_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨a.1.comp z (by omega), ?_⟩
      have ha : δ n (n + 1) (a : Cochain I K n) = 0 := Cocycle.δ_eq_zero _ _
      have hz' : δ (-1) 0 z = Cochain.ofHom f - Cochain.ofHom g := by rw [hz]; abel
      rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega)]
      simp only [ha, Cochain.zero_comp, smul_zero, add_zero, hz', Cochain.comp_sub]
      rfl

end LateralTheory.EtaleFoundations
end

