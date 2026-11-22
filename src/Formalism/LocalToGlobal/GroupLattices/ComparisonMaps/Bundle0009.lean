import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0004
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0003

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsRec
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

attribute [local irreducible] Formalism.L2.G.repP

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) (hdet : IsUnit sp.gram0.det) (hH : HypAtP I)

def clsR (i : compL L p) (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) : C.cls 0 :=
  clsOf L (clsC I hdet hk i Lt)

include hH in
theorem stab_card1 (i : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y = (repP L p i).1)
    (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) (h : ∀ v, IsLattice W (Lt v)) :
    Nat.card {γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y //
      (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ Lt = Lt} =
      Nat.card (C.stab 0 (clsR hk I hdet i Lt)) := by
  have h1 := (Nat.card_congr (fixEquiv hS r lam0 dom hk I ψ hdet hH i y hy (gOf Lt))).trans (card_stabU _)
  rw [← gOf_spec Lt h] at h1
  exact h1

include hH hdet in
theorem trivStab1 (hT : TrivStabU L) (i : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y = (repP L p i).1) (γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y)
    (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) (h : ∀ v, IsLattice W (Lt v))
    (hfix : (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ Lt = Lt) :
    γ = 1 := by
  rw [level_action_lattice_eq] at hfix
  have h1 := (fix_iff hk I hdet hH i (gOf Lt) γ.1).2 ⟨hy ▸ γ.2, by rw [← gOf_spec Lt h]; exact hfix⟩
  exact Subtype.ext (hT _ _ h1)

set_option maxHeartbeats 2000000 in
include hH in

theorem clsR_iff (i i' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp)
    (Lt Lt' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup)
    (h : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt)
    (h' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt') :
    clsR hk I hdet i Lt = clsR hk I hdet i' Lt' ↔
      i = i' ∧ ∃ γ : ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).Γ,
        Lt' = ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).smul γ Lt :=
  clsOf_inj.eq_iff.trans (clsC_iff hS r lam0 dom hk I ψ e hdet hH i i' Lt Lt' h h')

include hH in

theorem clsR_surj (c : C.cls 0) :
    ∃ (i : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp) (Lt : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup),
      (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt ∧ clsR hk I hdet i Lt = c := by
  obtain ⟨c', rfl⟩ := clsOf_surj (L := L) c
  obtain ⟨i, Lt, h1, h2⟩ := clsC_surj hS r lam0 dom hk I ψ e hdet hH c'
  exact ⟨i, Lt, h1, congrArg (clsOf L) h2⟩

set_option maxHeartbeats 2000000 in
include hH in

theorem stab_card (i : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp)
    (Lt : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup)
    (h : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt) :
    Nat.card {γ : ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).Γ //
      ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).smul γ Lt = Lt} = Nat.card (C.stab 0 (clsR hk I hdet i Lt)) :=
  stab_card1 hS r lam0 dom hk I ψ hdet hH i _ rfl Lt h

set_option maxHeartbeats 2000000 in
include hH hdet in

theorem trivStab (hT : TrivStabU L) : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).TrivStab :=
  fun i γ Lt h hfix => trivStab1 hS r lam0 dom hk I ψ hdet hH hT i _ rfl γ Lt h hfix

end Formalism.L2.G.Cmp
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct
section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reGL_apply {a b : ℕ} (h : a = b) (R : Type) [CommRing R] (g : GL (Fin a) R) (x y : Fin b) :
    (reGL h R g : Matrix (Fin b) (Fin b) R) x y = (g : Matrix (Fin a) (Fin a) R) (Fin.cast h.symm x) (Fin.cast h.symm y) := by
  rfl

theorem reGL_mem_UJ {a b : ℕ} (h : a = b) {R : Type} [CommRing R] (σ : R →+* R) (J : Matrix (Fin a) (Fin a) R)
    (J' : Matrix (Fin b) (Fin b) R) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) (g : GL (Fin a) R)
    (hg : g ∈ UJ σ J) : reGL h R g ∈ UJ σ J' := by
  subst h
  have hJ' : J' = J := by
    ext x y
    rw [hJ]
    simp
  subst hJ'
  have hg' : reGL rfl R g = g := by
    ext x y
    rw [reGL_apply]
    simp
  rw [hg']
  exact hg

theorem LocAt.actB_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ}
    {G : GAtP p} (A : LocAt F E n G) {k : ℕ} (hk : k = n) (B0 : GL (Fin k) E) (γ0 : ∀ i, (G.lev i).Γ → GL (Fin k) E)
    (hB : A.B = reGL hk E B0) (hγ : ∀ i γ, A.gamI i γ = reGL hk E (γ0 i γ))
    (hact : ∀ i v (γ : (G.lev i).Γ) (a b : Fin (G.P.m + 1)) (a' b' : Fin k), (a : ℕ) = a' → (b : ℕ) = b' →
      A.eQ v (((G.lev i).act v γ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) a b) =
        (((bc (A.phE v) B0)⁻¹ * bc (A.phE v) (γ0 i γ) * bc (A.phE v) B0 : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) a' b') :
    A.ActB := by
  intro i v γ
  have key : ((bc (A.phE v) B0)⁻¹ * bc (A.phE v) (γ0 i γ) * bc (A.phE v) B0 : GL (Fin k) _) =
      bc (A.phE v) (B0⁻¹ * γ0 i γ * B0) := by
    simp only [map_mul, map_inv]
  have key2 : (A.B⁻¹ * A.gamI i γ * A.B : GL (Fin n) E) = reGL hk E (B0⁻¹ * γ0 i γ * B0) := by
    rw [hB, hγ]
    simp only [map_mul, map_inv]
  have hiw : ∀ z, A.eQ v (A.iw v z) = A.phE v z := fun z => by
    simp [LocAt.iw]
  ext x y
  apply (A.eQ v).injective
  have h1 := hact i v γ (Fin.cast A.rk.symm x) (Fin.cast A.rk.symm y) (Fin.cast hk.symm x)
    (Fin.cast hk.symm y) rfl rfl
  rw [key] at h1
  rw [key2]
  exact h1.trans (hiw _).symm

variable {D : D7}

theorem embT_conj (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

theorem gramN_zero (D : D7) (x y : Fin (D.R.N 0)) :
    gramN D 0 (Nat.zero_le _) x y = D.sp.gram0 (Fin.cast (rank_eq_first_level D.R).symm x) (Fin.cast (rank_eq_first_level D.R).symm y) := rfl

variable {X : Formalism.L2.Herm.Herm0 D}

theorem locAt_UJ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) (i : (D.gat u w hg).comp) (γ : ((D.gat u w hg).lev i).Γ) :
    (locAt X u w hg B).gamI i γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := by
  exact reGL_mem_UJ (rank_eq_first_level D.R) (sigD D : D.host.E →+* D.host.E) D.sp.gram0 _ (fun x y => gramN_zero D x y) _
    ((X.g u w hg).gamI i γ).2

set_option maxHeartbeats 1000000 in

theorem locAt_actB (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) (hB : FrRat X u w hg B) : (locAt X u w hg B).ActB := by
  refine LocAt.actB_of (locAt X u w hg B) (rank_eq_first_level D.R) B
    (fun i γ => ((X.g u w hg).gamI i γ : GL (Fin D.R.k) D.host.E)) rfl (fun i γ => rfl) ?_
  intro i v γ a b a' b' ha hb
  have h1 := (X.g u w hg).act_eq i v _ rfl ((X.g u w hg).pl v).2 γ a b a' b' ha hb
  rw [hB _ ((X.g u w hg).pl v).2] at h1
  have hbc : bc ((RingHom.fst _ _).comp ((X.g u w hg).spl _ ((X.g u w hg).pl v).2).toRingHom)
      (bc (inclE (F := D.host.F) _) ((X.g u w hg).gamI i γ : GL (Fin D.R.k) D.host.E)) =
      bc (((RingHom.fst _ _).comp ((X.g u w hg).spl _ ((X.g u w hg).pl v).2).toRingHom).comp
        (inclE (F := D.host.F) _)) ((X.g u w hg).gamI i γ : GL (Fin D.R.k) D.host.E) := by
    ext x y
    rfl
  rw [hbc] at h1
  exact h1

theorem locAt_std (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) (hB : StdB D B) :
    cT (sigD D : D.host.E →+* D.host.E) (locAt X u w hg B).B.1 * gramN D 0 (Nat.zero_le _) * (locAt X u w hg B).B.1 = 1 := by
  exact hB.1

end Formalism.L2.G.Cmp

end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.SpanImageOfSurj
section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms NumberField

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (α : Type) {LL : Type} [Field LL] (e : LL →+* Kf) (Mi : Submodule O (FnP P α))

theorem span_image_of_surj {V : Type} [AddCommGroup V] [Module LL V] (cmp : V →ₛₗ[e] FnP P α) (A : Subring LL)
    (hA : ∀ a ∈ A, e a ∈ Set.range (algebraMap O Kf)) (S : Set V)
    (hsurj : ∀ F ∈ Mi, RatFnP P α e F → ∃ x, cmp x = F)
    (hlat : ∀ x, cmp x ∈ Mi ↔ x ∈ Submodule.span A S) (hd : MRatSpan P α e Mi) :
    Submodule.span O (cmp '' S) = Mi := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    exact (hlat s).mpr (Submodule.subset_span hs)
  · have key : ∀ v ∈ Submodule.span A S, cmp v ∈ Submodule.span O (cmp '' S) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        obtain ⟨o, ho⟩ := hA a a.2
        have h1 : cmp (a • x) = o • cmp x := by
          rw [show a • x = (a : LL) • x from rfl, LinearMap.map_smulₛₗ, ← ho, algebraMap_smul]
        rw [h1]
        exact Submodule.smul_mem _ o hx
    rw [← hd, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨v, hv⟩ := hsurj _ hx (cmpF_rat P α e Mi x)
    rw [← hv]
    exact key v ((hlat v).mp (by rw [hv]; exact hx))

end Gen

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

structure CmpHypR (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop where
  ex : ∀ u w hg, ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y
  uniq : ∀ u w hg, ValUniq ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y
  pos : ∀ u w hg v (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
    I.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
      (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) ((locAt X u w hg I.B).iw v x))
  chi : ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

  inj : ∀ u w hg, Function.Injective (cmpRec T Gt I u w hg)

  surj : ∀ u w hg, ∀ F ∈ (D.gat u w hg).M, RatFn (D.gat u w hg) (I.embW u w hg) F → ∃ x, cmpRec T Gt I u w hg x = F

  lat : ∀ u w hg x, cmpRec T Gt I u w hg x ∈ (D.gat u w hg).M ↔ x ∈ locW D.what₂.places w ((D.fm u).lat 0).L

  desc : ∀ u w hg, MRatSpan (D.gat u w hg).P (D.gat u w hg).comp (I.embW u w hg) (D.gat u w hg).M

theorem cmpRec_rat (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (x : ((D.fm u).lat 0).V) :
    RatFn (D.gat u w hg) (I.embW u w hg) (cmpRec T Gt I u w hg x) := by
  intro i L
  unfold cmpRec cmpC
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, map_zero _⟩

theorem CmpHypR.hyp {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X} (H : CmpHypR T Gt I) :
    CmpHyp T Gt I where
  ex := H.ex
  uniq := H.uniq
  pos := H.pos
  chi := H.chi
  li := fun u w hg =>
    li_of_rat (I.embW u w hg) (evG (D.gat u w hg))
      (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)).toAddMonoidHom (evG_sep _)
      (fun a x => (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)).map_smulₛₗ a x)
      (fun x => (ratFn_iff _ _ _).1 (cmpRec_rat T Gt I u w hg x)) (H.inj u w hg) _
      ((D.fm u).lat 0).b.linearIndependent
  latM := fun u w hg =>
    span_image_of_surj (D.gat u w hg).P (D.gat u w hg).comp (I.embW u w hg) (D.gat u w hg).M
      (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)) (intW D.what₂.places w)
      (fun a ha => (I.embW_int u w hg a).1 ha) _ (H.surj u w hg) (H.lat u w hg) (H.desc u w hg)

end Formalism.L2.G.Cmp
end
end

