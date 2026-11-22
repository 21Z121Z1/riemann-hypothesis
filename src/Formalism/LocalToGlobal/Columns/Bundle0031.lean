import Formalism.LocalToGlobal.Columns.Bundle0029
import Formalism.LocalToGlobal.Columns.TiedHK
import Formalism.LocalToGlobal.Columns.Bundle0014
import Formalism.LocalToGlobal.Columns.Bundle0030
import Formalism.LocalToGlobal.Columns.Bundle0027
import Formalism.LocalToGlobal.Columns.WordFin
import Formalism.LocalToGlobal.Columns.TiedPer
import Formalism.LocalToGlobal.Columns.TiedValFi
import Formalism.LocalToGlobal.Columns.Bundle0028
import Formalism.LocalToGlobal.Columns.TiedValDil

-- bundled from Formalism.LocalToGlobal.Columns.CoordLatticeSelfDualEqStd
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

include hX hPr in

theorem localLevelIsKOneAtT_holds : LocalLevelIsKOneAtT hc u Λ := fun v hv x =>
  localLevel_iff_kOne hc n Pr.vGs Λ.grp v (basePi_of_ok hX hPr u) (rls_T_notUnder hPr u v hv) x

variable (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem th_reL_std {E : Type} [Field E] [NumberField E] {a b : ℕ} (h : a = b) :
    Formalism.L2.Forms.reL h (stdLat E a) = stdLat E b := by
  subst h
  exact Formalism.L2.Forms.reL_rfl _

theorem levPack_base (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) (pb : 𝓞 X.E)
    (hpb : algebraMap (𝓞 X.E) X.E pb = star (algebraMap (𝓞 X.E) X.E (Pr.piT u))) :
    (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 X.E)
      (dualSet (hc.sig : X.E →+* X.E) H.J (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb) = stdLat X.E H.n' := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact th_base_companion hc _ (basePi_of_ok hX hPr u) pb hpb

end Gen

theorem th_map_span_std {E V : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] {r r' : ℕ} (e : V ≃ₗ[E] (Fin r → E)) (b : Fin r' → V) (σ : Fin r' ≃ Fin r)
    (hb : ∀ a, e (b a) = Pi.single (σ a) (1 : E)) :
    (Submodule.span (𝓞 E) (Set.range b)).map ((e : V →ₗ[E] (Fin r → E)).restrictScalars (𝓞 E)) = stdLat E r := by
  rw [Submodule.map_span, ← Set.range_comp]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    show e (b a) ∈ _
    rw [hb]
    simpa using single_mem_stdLat (E := E) (σ a) 1
  · intro x hx
    rw [mem_stdLat] at hx
    choose t ht using hx
    have hsum : x = ∑ j, t j • e (b (σ.symm j)) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [hb, Equiv.apply_symm_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one, ht]
      · intro j _ hj
        rw [hb, Equiv.apply_symm_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

variable {d : ColDat}

theorem localLevelIsKOne_everywhere (d : ColDat) : LocalLevelIsKOneEverywhere d := fun u i => localLevelIsKOneAtT_holds d.sp.cm d.hX d.hPr u (d.lev i)

theorem coordLattice_selfDual_eq_std (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) :
    Formalism.L2.Herm.crdLat (d.sp.X i) (d.sp.X i).L0 = stdLat d.X.E (d.sp.X i).rank := by
  unfold Formalism.L2.Herm.crdLat
  rw [hS.selfDual_span_frame_X i hi]
  refine th_map_span_std (Formalism.L2.Herm.crd (d.sp.X i)) _ (Equiv.refl _) fun a => ?_
  funext j
  show (d.sp.X i).frame.equivFun ((d.sp.X i).frame a) j = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext eq_comm

theorem coordLattice_selfDual_zero (hS : SpStd d.toColBase) : d.sp.crdLat0 (d.sp.X 0).L0 = stdLat d.X.E d.R.k := by
  unfold Spaces.crdLat0
  rw [hS.selfDual_span_frame_X 0 (Nat.zero_le _)]
  refine th_map_span_std d.sp.crd0 _ (finCongr d.sp.rank0) fun a => ?_
  funext j
  show (d.sp.X 0).frame.equivFun ((d.sp.X 0).frame a) ((finCongr d.sp.rank0).symm j) = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext ⟨fun h => by rw [h, Equiv.apply_symm_apply], fun h => by rw [h, Equiv.symm_apply_apply]⟩

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MtHeckeKv
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt)

section Kv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n]

def mhlKv (v : HeightOneSpectrum (𝓞 F)) : Subgroup (UAd hc n) where
  carrier := {η | (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      bc (prV (E := E) w) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
    bc (prV (E := E) v) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))}
  one_mem' := ⟨fun w _ => by rw [OneMemClass.coe_one, map_one], by rw [OneMemClass.coe_one, map_one]; exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Subgroup.coe_mul, map_mul, ha1 w hw, hb1 w hw, mul_one]
    · rw [Subgroup.coe_mul, map_mul]; exact mul_mem ha2 hb2
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [InvMemClass.coe_inv, map_inv, ha1 w hw, inv_one]
    · rw [InvMemClass.coe_inv, map_inv]; exact inv_mem ha2

variable {hc n}

theorem mem_mhlKv_iff {v : HeightOneSpectrum (𝓞 F)} {η : UAd hc n} :
    η ∈ mhlKv hc n v ↔ (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      bc (prV (E := E) w) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
    bc (prV (E := E) v) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) :=
  Iff.rfl

theorem mhl_eq_put {v : HeightOneSpectrum (𝓞 F)} {η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hη : η ∈ UAd hc n)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) η = 1) :
    η = rll_put n v (bc (prV (E := E) v) η) := by
  have h1 : (afsplitE hc.sig (1 : Matrix (Fin n) (Fin n) E) v ⟨η, hη⟩).2 = 1 :=
    (afsplitE_snd_eq_one hc.sig 1 v ⟨η, hη⟩).2 h
  have h2 : afsplitU v 1 η = 1 := by
    rw [← afsplitE_snd hc.sig (1 : Matrix (Fin n) (Fin n) E) v ⟨η, hη⟩]
    exact congrArg Subtype.val h1
  conv_lhs => rw [← afsplit_left v η, h2]
  rfl

variable (ST SG : Finset (Pl E))

theorem put_mem_kOne_of_not_over {v : HeightOneSpectrum (𝓞 F)} (hST : ∀ P ∈ ST, ¬ IsOver v P) (hSG : ∀ P ∈ SG, ¬ IsOver v P)
    {g : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hU : rll_put n v g ∈ UAd hc n)
    (hg : g ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))) : rll_put n v g ∈ K1 hc n ST SG := by
  have hS := rll_put_mem_St n v hg
  have hJ : rll_put n v g ∈ J0 hc n ST := by
    refine ⟨⟨hU, hS⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => ?_⟩
    refine ⟨⟨rll_put n v g, hS⟩, ?_, rfl⟩
    show redAt 1 P ⟨rll_put n v g, hS⟩ ∈ mirab (kP P) n
    rw [rll_put_red n v g hS P (hST P hP)]
    exact one_mem _
  refine ⟨⟨_, hJ⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
  funext w
  exact rll_put_red n v g hS w.1 (hSG w.1 w.2)

theorem localLevel_le_kOne {v : HeightOneSpectrum (𝓞 F)} (hST : ∀ P ∈ ST, ¬ IsOver v P) (hSG : ∀ P ∈ SG, ¬ IsOver v P)
    {η : UAd hc n} (hη : η ∈ mhlKv hc n v) : (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ K1 hc n ST SG := by
  have e := mhl_eq_put η.2 hη.1
  rw [e] at ⊢
  exact put_mem_kOne_of_not_over ST SG hST hSG (e ▸ η.2) hη.2

theorem decoOf_mul_mhlKv {v : HeightOneSpectrum (𝓞 F)} (hST : ∀ P ∈ ST, ¬ IsOver v P) (hSG : ∀ P ∈ SG, ¬ IsOver v P)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {η : UAd hc n} (hη : η ∈ mhlKv hc n v) :
    decoOf ST SG (x * (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) = decoOf ST SG x :=
  decoration_mul_principal hc n ST SG x (localLevel_le_kOne ST SG hST hSG hη)

theorem mem_localLevel_of_mem_kOne {v : HeightOneSpectrum (𝓞 F)} {η : UAd hc n}
    (h1 : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (hK : (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ K1 hc n ST SG) : η ∈ mhlKv hc n v := by
  refine ⟨h1, ?_⟩
  have hS : (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
    congruence_subgroup_le_stabilizer hc n ST (principal_le_congruence_subgroup hc n ST SG hK)
  rw [St_one] at hS
  exact Formalism.L2.DIV.lc_stab_loc v (stdLat E n) _ hS

theorem mhl_inv_mul_mem {v : HeightOneSpectrum (𝓞 F)} (x g g' : UAd hc n)
    (hg : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (hg' : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (g' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (h : decoOf ST SG ((x * g : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      decoOf ST SG ((x * g' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    g⁻¹ * g' ∈ mhlKv hc n v := by
  have hr : decoRaw ST SG ((x * g : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      decoRaw ST SG ((x * g' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [← rlc_decoOf_val hc n ST SG (x * g).2, ← rlc_decoOf_val hc n ST SG (x * g').2, h]
  have hK := mem_principal_of_same_decoration hc n ST SG (x * g).2 (x * g').2 hr
  have e : ((x * g : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * ((x * g' : UAd hc n) : GL (Fin n) _) =
      ((g⁻¹ * g' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, _root_.mul_inv_rev]
    group
  rw [e] at hK
  refine mem_localLevel_of_mem_kOne ST SG (fun w hw => ?_) hK
  rw [Subgroup.coe_mul, InvMemClass.coe_inv, map_mul, map_inv, hg w hw, hg' w hw, inv_one, one_mul]

end Kv

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedHIw
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG
open Formalism.L2.Forms (kv redM InJ aOf fcOf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : CMData F E) (n : ℕ) [NeZero n] (ST : Finset (Pl E))
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

theorem hiw_levelVL_iff (hsig : ∀ x, spl (sigR hc.sig (v.adicCompletion F) x) = swapR _ (spl x))
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (hT : v ∉ plUnder F ST)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F)) :
    x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ↔
      bc (gloPhi v spl) x ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring := by
  have hu : ∃ u ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring,
      (u : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
        fun i j => (spl (inclE (F := F) (v.adicCompletion F) ((1 : Matrix (Fin n) (Fin n) E) i j))).1 := by
    refine ⟨1, one_mem _, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have h1 := Formalism.UG.P.level_subgroup_split F E (Fin n) hc.sig (1 : Matrix (Fin n) (Fin n) E) v spl hsig
    (Formalism.L2.G.split_integral_completion F E v spl halg) hu x hx
  rw [← Formalism.UG.P.level_subgroup_local_standard F E (Fin n) hc.sig (1 : Matrix (Fin n) (Fin n) E) v] at h1
  refine Iff.trans ?_ h1
  have e : latS (F := F) (v.adicCompletion F) (intV E v) (baseLb E n ST) =
      latS (F := F) (v.adicCompletion F) (intV E v) (Formalism.UG.stdLat (n := Fin n) (A := E) (𝓞 E)) := by
    have := rll_locL_base (F := F) n ST v hT
    rw [stdLat_eq_ug] at this
    exact this
  unfold levelVL
  rw [show latS (F := F) (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E)
    (v.adicCompletionIntegers F).toSubring) (baseLb E n ST) = _ from e]

end Gen

theorem inLevelZero_iff_unitriangular (R : Ranks) {κ : Type} [Field κ] (M : Matrix (Fin (R.N 0)) (Fin (R.N 0)) κ) :
    InJ (aOf R 0) R.t (fcOf R 0) (decide (0 = R.m)) M ↔ ∀ p q : Fin (R.N 0), (q < p → M p q = 0) ∧ M p p = 1 := by
  have hm := R.two_le_m
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have ha : aOf R 0 = R.k := by unfold aOf; rw [if_pos (by omega)]; rfl
  have hf : fcOf R 0 = R.N 0 := if_neg (by omega)
  have hd : decide (0 = R.m) = false := decide_eq_false (by omega)
  have hb : ∀ x : Fin (R.N 0), Formalism.L2.Forms.blkOf (aOf R 0) R.t x = x := fun x => by
    unfold Formalism.L2.Forms.blkOf; rw [if_pos (by rw [ha, ← hN]; exact x.2)]
  rw [hd, hf]
  constructor
  · rintro ⟨h1, h2, -, -⟩ p q
    exact ⟨fun hqp => h1 p q (by rw [hb, hb]; exact hqp), h2 p (by rw [ha, ← hN]; exact p.2)⟩
  · intro h
    refine ⟨fun x y hxy => (h x y).1 (by rw [hb, hb] at hxy; exact hxy), fun x _ => (h x x).2, ?_, ?_⟩
    · intro x y hy
      exact absurd hy (Nat.ne_of_lt y.2)
    · intro hh
      exact absurd hh (by simp)

section Clo

theorem hiw_closure {κ κ' : Type} [Field κ] [Field κ'] (e : κ ≃+* κ') {n : ℕ} (H : Subgroup (GL (Fin n) κ))
    (hH : ∀ M : GL (Fin n) κ, M ∈ H ↔ ∀ p q : Fin n, (q < p → (M : Matrix (Fin n) (Fin n) κ).map e p q = 0) ∧
      (M : Matrix (Fin n) (Fin n) κ).map e p p = 1)
    (y : GL (Fin n) κ') (hy : y ∈ Subgroup.closure (upperUni n κ')) :
    ∃ M ∈ H, (M : Matrix (Fin n) (Fin n) κ).map e = (y : Matrix (Fin n) (Fin n) κ') := by
  have hle : Subgroup.closure (upperUni n κ') ≤ H.map (bc (e : κ →+* κ')) := by
    rw [Subgroup.closure_le]
    intro z hz
    let M : GL (Fin n) κ := bc (e.symm : κ' →+* κ) z
    have hMz : (M : Matrix (Fin n) (Fin n) κ).map e = (z : Matrix (Fin n) (Fin n) κ') := by
      funext p q
      exact e.apply_symm_apply _
    refine ⟨M, (hH M).2 ?_, Units.ext hMz⟩
    rw [hMz]
    exact hz
  obtain ⟨M, hM, hMy⟩ := hle hy
  exact ⟨M, hM, congrArg Units.val hMy⟩

end Clo

section Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (Ch : Chars X Pr R.m)
  (S : GSplit (Pr := Pr) hc) (u : Pr.Word)

theorem hiw_red {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (v.adicCompletionIntegers F))
    (p q : Fin n) :
    ((redGL (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) g :
      GL (Fin n) ((v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))) :
      Matrix (Fin n) (Fin n) ((v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))) p q =
    (redM F v ((bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q :
      (v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) := by
  have hm : ((bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q ∈ v.adicCompletionIntegers F :=
    ((g : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)) p q).2
  simp only [redM]
  rw [dif_pos hm]
  rfl

include hX hPr in
set_option maxHeartbeats 1000000 in

theorem iwLoc : IwLoc hc u (colLevS Ch 0) S.sp := by
  intro i v h x hxU
  rw [inv_one, one_mul, mul_one]
  have hbad : v ∈ plUnder X.F Pr.vGs :=
    (th_plUnder_vGs hc hPr v).2 (by fin_cases i; exact Or.inl h; exact Or.inr h)
  have hT : v ∉ plUnder X.F (Pr.vT u) := fun hT =>
    rls_T_notUnder hPr u v ((mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).1 hT) hbad
  have hlv := hiw_levelVL_iff hc (R.N 0) (Pr.vT u) v (S.sp i v h) (S.sp_sig i v h) (S.sp_alg i v h) hT x hxU
  have hmem : x ∈ levelVL hc.sig (1 : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.E) v (baseLb X.E (R.N 0) (Pr.vT u)) →
      (x ∈ levLoc hc (R.N 0) (Pr.vT u) Pr.vGs (colLevS Ch 0).grp v ↔
        ∃ M ∈ (colLevS Ch 0 (gwOf hc hPr i v h)).H, (M : Matrix (Fin (R.N 0)) (Fin (R.N 0)) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h) =
          redM X.F v ((bc (gloPhi v (S.sp i v h)) x : GL (Fin (R.N 0)) (v.adicCompletion X.F)) :
            Matrix (Fin (R.N 0)) (Fin (R.N 0)) (v.adicCompletion X.F))) :=
    fun hx => gco_mem_levLoc hc (R.N 0) (Pr.vT u) Pr.vGs v (S.sp i v h) (S.sp_alg i v h)
      (fun w => (colLevS Ch 0 w).H) (gwOf hc hPr i v h) (S.ker hPr i v h) (gwOf_over hc hPr i v h)
      (gwOf_uniq hc hPr i v h) hT x hx
  have hH : ∀ M : GL (Fin (R.N 0)) (kP (gwOf hc hPr i v h).1), M ∈ (colLevS Ch 0 (gwOf hc hPr i v h)).H ↔
      ∀ p q : Fin (R.N 0), (q < p → (M : Matrix (Fin (R.N 0)) (Fin (R.N 0)) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h) p q = 0) ∧
        (M : Matrix (Fin (R.N 0)) (Fin (R.N 0)) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h) p p = 1 :=
    fun M => (colLevS_mem_iff Ch (Nat.zero_le _) _ (S.eK hPr i v h) M).trans (inLevelZero_iff_unitriangular R _)
  constructor
  · intro hx
    have hlev := levLoc_le_levelVL hc (R.N 0) (Pr.vT u) Pr.vGs _ v hx
    obtain ⟨M, hM, hMx⟩ := (hmem hlev).1 hx
    obtain ⟨g, hg⟩ := hlv.1 hlev
    have hI := (hH M).1 hM
    rw [hMx] at hI
    have hgx : ((bc (algebraMap (v.adicCompletionIntegers X.F) (v.adicCompletion X.F)) g : GL (Fin (R.N 0)) (v.adicCompletion X.F)) :
        Matrix (Fin (R.N 0)) (Fin (R.N 0)) (v.adicCompletion X.F)) =
        ((bc (gloPhi v (S.sp i v h)) x : GL (Fin (R.N 0)) (v.adicCompletion X.F)) :
          Matrix (Fin (R.N 0)) (Fin (R.N 0)) (v.adicCompletion X.F)) := congrArg Units.val hg
    refine Subgroup.mem_map.2 ⟨g, ?_, hg⟩
    apply Subgroup.subset_closure
    intro p q
    exact ⟨fun hqp => by rw [hiw_red, hgx]; exact (hI p q).1 hqp, by rw [hiw_red, hgx]; exact (hI p p).2⟩
  · intro hx
    obtain ⟨g, hgU, hg⟩ := Subgroup.mem_map.1 hx
    have hlev : x ∈ levelVL hc.sig (1 : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.E) v (baseLb X.E (R.N 0) (Pr.vT u)) :=
      hlv.2 ⟨g, hg⟩
    have hgx : ((bc (algebraMap (v.adicCompletionIntegers X.F) (v.adicCompletion X.F)) g : GL (Fin (R.N 0)) (v.adicCompletion X.F)) :
        Matrix (Fin (R.N 0)) (Fin (R.N 0)) (v.adicCompletion X.F)) =
        ((bc (gloPhi v (S.sp i v h)) x : GL (Fin (R.N 0)) (v.adicCompletion X.F)) :
          Matrix (Fin (R.N 0)) (Fin (R.N 0)) (v.adicCompletion X.F)) := congrArg Units.val hg
    refine (hmem hlev).2 ?_
    obtain ⟨M, hM, hMg⟩ := hiw_closure (κ' := kv X.F v) (S.eK hPr i v h) _ hH
      (redGL (IsLocalRing.maximalIdeal (v.adicCompletionIntegers X.F)) g) hgU
    refine ⟨M, hM, hMg.trans ?_⟩
    funext p q
    rw [← hgx]
    exact hiw_red v g p q

end Col

theorem iwAll (d : ColDat) (S : GSplit (Pr := d.Pr) d.sp.cm) : IwAll d S :=
  fun u => by
    rw [d.lev0, ← colLevS_of_lt d.Ch (Nat.lt_of_lt_of_le (by norm_num) d.R.two_le_m)]
    exact iwLoc d.sp.cm d.hX d.hPr d.Ch S u

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedPerDat
section
noncomputable section

namespace Formalism.L2.Col

theorem per_onto_dat (d : ColDat) (a : ColArgs d) :
    (∀ z ∈ (ptEv (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx).Fi, ∃ F, jMCL (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx a.rowOk F = z) ∧
      ∀ F, jMCL (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx a.rowOk F ∈ (ptEv (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx).Fi :=
  ⟨fun z hz => per_jMC_onto (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx a.rowOk d.hX z hz,
    fun F => per_jMC_mem_Fi (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx a.rowOk d.hX F⟩

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedValAll
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ)
  (hi : i ≤ d.R.m)

def valuationAgreementConcrete : CF.ValTied (D := d.colRec a) u (atTTied a hH u).eV i hi (classAgreement a hS hH hP u i hi) :=
  valuationAgreement a hS hH hP u i hi (tieEV d.sp.cm d.hX d.hPr u)
    (Val.fi (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
      (valCrd a hS hH u i hi))
    (Val.rat (Pr := d.Pr) d.W d.lev d.hX d.σ₀ d.star_cx u i (valCrd a hS hH u i hi))
    (Val.lat (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.σ₀ d.star_cx u i d.what₂.places d.plEq d.plEq.surjective hH.val_eq
      (valCrd a hS hH u i hi))
    (Val.dil (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
      (tieEV d.sp.cm d.hX d.hPr u) (tieEV_over d.sp.cm d.hX d.hPr u) (valCrd a hS hH u i hi))
    (Val.dilT (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
      (tieEV d.sp.cm d.hX d.hPr u) (tieEV_over d.sp.cm d.hX d.hPr u) (valCrd a hS hH u i hi))

theorem stepValTied_eY : (valuationAgreementConcrete a hS hH hP u i hi).eY = valEY (Pr := d.Pr) d.W d.lev d.σ₀ u i (valCrd a hS hH u i hi) := rfl

theorem stepNormTie : CF.NormTie (valuationAgreementConcrete a hS hH hP u i hi) :=
  normTie a hS hH hP u i hi _ (valuationAgreementConcrete a hS hH hP u i hi) rfl

theorem stepBwTie : CF.BwTie (atTTied a hH u) (valuationAgreementConcrete a hS hH hP u i hi) :=
  bwTie_of a hS hH hP u i hi (valuationAgreementConcrete a hS hH hP u i hi) rfl
    (Val.bw (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i d.what₂.places d.plEq hH.val_eq (valCrd a hS hH u i hi)
      (atTTied a hH u).Pv (fun _ => Ideal.mk_ker))

end Formalism.L2.Col
end
end

