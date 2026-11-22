import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivGroupTateLieCompat
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.HodgeTateCokernel

theorem exists_retraction_range {p : ℕ} [Fact p.Prime] {M M' : Type} [CommGroup M] [CommGroup M']
    (f : M →* M') (hf : Function.Injective f) [Module.Finite ℤ_[p] (HTLat.Tate p M')] :
    ∃ r : HTLat.Tate p M' →ₗ[ℤ_[p]] LinearMap.range (HTLat.Tate.map p f),
      ∀ s : LinearMap.range (HTLat.Tate.map p f), r s = s := by
  set S := LinearMap.range (HTLat.Tate.map p f)
  have h1 : ∀ t, (p : ℤ_[p]) • t ∈ S → t ∈ S := by
    rintro t ⟨u, hu⟩
    have h : ∀ n, f (u.lev (n + 1)) = t.lev n := fun n => by
      rw [← HTLat.Tate.lev_map, hu, HTLat.Tate.lev_smul, PDiv.pow_digit_natCast (t.lev_pow _),
        t.lev_succ]
    exact ⟨HTLat.Tate.mk (fun n => u.lev (n + 1)) fun n =>
      ⟨hf (by rw [map_pow, h, t.lev_pow, map_one]), u.lev_succ _⟩, HTLat.Tate.ext h⟩
  have h2 : ∀ (n : ℕ) t, (p : ℤ_[p]) ^ n • t ∈ S → t ∈ S := fun n => by
    induction n with
    | zero => simp
    | succ n ih => exact fun t ht => h1 t (ih _ (by rwa [smul_smul, ← pow_succ]))
  haveI : Module.IsTorsionFree ℤ_[p] (HTLat.Tate p M' ⧸ S) := .of_smul_eq_zero fun a q h => by
    by_cases ha : a = 0
    · exact .inl ha
    obtain ⟨t, rfl⟩ := S.mkQ_surjective q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      PadicInt.unitCoeff_spec ha, mul_smul] at h
    exact .inr ((Submodule.Quotient.mk_eq_zero _).2
      (h2 _ t ((S.smul_mem_iff' (PadicInt.unitCoeff ha)).1 h)))
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property S.mkQ LinearMap.id S.mkQ_surjective
  refine ⟨(LinearMap.id - σ ∘ₗ S.mkQ).codRestrict S fun t => ?_, fun s => Subtype.ext ?_⟩
  · change s.1 - σ (S.mkQ s.1) = s.1
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 s.2, map_zero, sub_zero]
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub]
    exact sub_eq_zero.2 (LinearMap.congr_fun hσ (S.mkQ t)).symm

theorem dual_ext {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] {q : O} (hq : q ≠ 0)
    {s : Set M} (hs : ∀ w : M, q • w ∈ Submodule.span O s) {y z : Module.Dual O M}
    (h : ∀ m ∈ s, y m = z m) : y = z := LinearMap.ext fun w => by
  have h1 : y (q • w) = z (q • w) := LinearMap.eqOn_span (s := s) h (hs w)
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
  exact mul_left_cancel₀ hq h1

theorem cokernelBound_of_group : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∀ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) → (∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) → (∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x) → Module.Finite O G.omega → Module.Free O G.omega → (∀ w : G.omega, (p : O) ^ 2 • w ∈ Submodule.span O (Set.range (dlog (G := G)))) → CokernelBound P := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P G e l c ζ hζ hpair hdlog hfin hfree hspan f
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI : IsIntegrallyClosed O := P.integers.isIntegrallyClosed
  have hflip : Function.Bijective (pairT P.A P.eps).flip := by
    have h : (pairT P.A P.eps).flip = -pairT P.A P.eps :=
      LinearMap.ext₂ fun s t => ((isAlt_pairT P.A P.eps).neg_eq s t).symm
    rw [h]
    exact neg_bijective.comp P.pairT_bijective
  obtain ⟨r, hr⟩ : ∃ r : P.T →ₗ[ℤ_[p]] P.tateGt, ∀ s : P.tateGt, r s = s := by
    have h : Module.Finite ℤ_[p] P.T := inferInstance
    unfold Point.tateGt
    exact @exists_retraction_range p _ _ _ (_) (_) _ P.toA_injective h
  let u : ℤ_[p] ≃ₗ[ℤ_[p]] (PDivGroup.mu p O).Tate :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ ζ) hζ
  have hc : Function.Surjective c := fun χ => by
    obtain ⟨t, ht⟩ := hflip.2
      (u.symm.toLinearMap ∘ₗ (pairing G O).flip χ ∘ₗ e.symm.toLinearMap ∘ₗ r)
    refine ⟨t, (PDivGroup.tate_free_perfect p O C G).2.2.2.2.2.2.2.1 (LinearMap.ext fun s => ?_)⟩
    have h1 : pairT P.A P.eps (e s : P.T) t = u.symm (pairing G O (e.symm (r (e s : P.T))) χ) :=
      LinearMap.congr_fun ht (e s : P.T)
    rw [hr, LinearEquiv.symm_apply_apply] at h1
    change pairing G O s (c t) = pairing G O s χ
    rw [hpair, h1]
    exact u.apply_symm_apply _
  have hp : (p : O) ^ 2 ≠ 0 := pow_ne_zero _ fun h => by
    have h1 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h1
  have hext : ∀ {y z : G.Lie}, (∀ t, y (dlog (G := G) (c t)) = z (dlog (G := G) (c t))) → y = z :=
    fun h => dual_ext hp hspan (by
      rintro _ ⟨χ, rfl⟩
      obtain ⟨t, rfl⟩ := hc χ
      exact h t)
  have hadd : ∀ x y, l (lieAdd x y) = l x + l y := fun x y => hext fun t => by
    rw [LinearMap.add_apply, hdlog, hdlog, hdlog, omega_lieAdd]
  have hsc : ∀ (a : O) x, l (AvDefs.lieScale P.Gt a x) = a • l x := fun a x => hext fun t => by
    rw [LinearMap.smul_apply, hdlog, hdlog, omega_lieScale, smul_eq_mul]
  let F : Module.Dual O (Module.Dual O G.omega) :=
    { toFun := fun y => f.1 (l.symm y)
      map_add' := fun y z => by
        rw [← omega_lieAdd, l.symm_apply_eq.2 ((hadd (l.symm y) (l.symm z)).trans
          (by rw [l.apply_symm_apply, l.apply_symm_apply])).symm]
      map_smul' := fun a y => by
        rw [RingHom.id_apply, smul_eq_mul, ← omega_lieScale,
          l.symm_apply_eq.2 ((hsc a (l.symm y)).trans (by rw [l.apply_symm_apply])).symm] }
  obtain ⟨w, hw⟩ := (Module.bijective_dual_eval O G.omega).2 F
  have hfw : ∀ x, l x w = f.1 x := fun x => by
    have h1 : l x w = f.1 (l.symm (l x)) := LinearMap.congr_fun hw (l x)
    rwa [l.symm_apply_apply] at h1
  have key : ∀ m ∈ Submodule.span O (Set.range (dlog (G := G))),
      ∃ g ∈ LinearMap.range P.al, ∀ x, l x m = g.1 x := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨χ, rfl⟩ := hm
      obtain ⟨t, rfl⟩ := hc χ
      exact ⟨P.al₀ t, ⟨1 ⊗ₜ t, by rw [Point.al_tmul, one_smul]⟩, fun x => hdlog x t⟩
    | zero => exact ⟨0, zero_mem _, fun x => map_zero _⟩
    | add m n _ _ hm hn =>
      obtain ⟨g, hg, h⟩ := hm
      obtain ⟨g', hg', h'⟩ := hn
      exact ⟨g + g', add_mem hg hg', fun x => by rw [map_add, h, h']; rfl⟩
    | smul a m _ hm =>
      obtain ⟨g, hg, h⟩ := hm
      exact ⟨a • g, Submodule.smul_mem _ a hg, fun x => by rw [map_smul, h]; rfl⟩
  obtain ⟨g, hg, h⟩ := key _ (hspan w)
  have h2 : (p : O) ^ 2 • f = g := Subtype.ext (funext fun x => by
    rw [← h, map_smul, hfw]; rfl)
  rw [h2]
  exact hg

end GlobalTheory.HodgeTateCokernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinsMerge
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Merge

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

def comap {Tp Tp' : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (f : Tp' → Tp) : OMDat C R i Tp' (fun t => tup (f t)) where
  c' := O.c'
  hle := O.hle
  jL := O.jL
  hV := O.hV
  c0' := O.c0'
  lev := O.lev
  dδ := fun t => O.dδ (f t)
  Cl' := fun t => O.Cl' (f t)
  fCl := fun t => O.fCl (f t)
  bad := fun t => O.bad (f t)
  Lh := fun t => O.Lh (f t)
  La := fun t => O.La (f t)
  Nc := fun t => O.Nc (f t)
  gam := fun t => O.gam (f t)
  vol := fun t => O.vol (f t)
  ep := fun t => O.ep (f t)
  B := fun t => O.B (f t)
  epF := fun t => O.epF (f t)
  io := O.io
  hw := O.hw
  φ := fun t => O.φ (f t)
  w := fun t => O.w (f t)
  U₂ := fun t => O.U₂ (f t)
  dict₂ := fun t => O.dict₂ (f t)
  xi := fun t => O.xi (f t)
  thAd := fun t => O.thAd (f t)
  Plc := fun t => O.Plc (f t)

theorem pins_comap {Tp Tp' : Type} {tup : Tp → T0} {O : OMDat C R i Tp tup} (f : Tp' → Tp) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) : (comap O f).Pins κ v₀ ι x₀ :=
  ⟨h.lift, fun t => h.tuple (f t), h.act, fun t => h.bad (f t), fun t => h.reps (f t), fun t => h.ep (f t), h.io,
    fun t => h.w (f t), fun t => h.cov (f t), h.cxi.imp fun _ hc => ⟨hc.1, fun t => hc.2 (f t)⟩, fun t => h.model₂ (f t)⟩

variable {J : Type} {tup : J → T0} (src : ∀ j, OMDat C R i Unit (fun _ => tup j)) (c₃ : Coeff C.Q.l) (h₃ : C.Q.c.F ≤ c₃.F)
  (hs : ∀ j, (src j).c'.F ≤ c₃.F) (jL₃ : D.what₂.LL →+* c₃.F) (hV₃ : C.V ((i : ℕ) + 1) (sOv C c₃ h₃) = Wc D i)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (u : J → c₃.F) (h : ∀ j, (src j).Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)

def merge : OMDat C R i J tup where
  c' := c₃
  hle := h₃
  jL := jL₃
  hV := hV₃
  c0' := c0₃
  lev := lev
  dδ := fun j => covBC (hs j) ((src j).dδ ()) (u j)
  Cl' := fun j => (src j).Cl' ()
  fCl := fun j => (src j).fCl ()
  bad := fun j => (src j).bad ()
  Lh := fun j => (src j).Lh ()
  La := fun j => (src j).La ()
  Nc := fun j => (src j).Nc ()
  gam := fun j => (src j).gam ()
  vol := fun j => incF _ c₃ (hs j) ((src j).vol ())
  ep := fun j k => incF _ c₃ (hs j) ((src j).ep () k)
  B := fun j I => incF _ c₃ (hs j) ((src j).B () I)
  epF := fun j L => incF _ c₃ (hs j) ((src j).epF () L)
  io := io₃
  hw := hw₃
  φ := fun j x => incF _ c₃ (hs j) ((src j).φ () x)
  w := fun j k q => incF _ c₃ (hs j) ((src j).w () k q)
  U₂ := fun j => covUnf (hs j) ((src j).dδ ()) (u j) ((src j).U₂ ())
  dict₂ := fun j => (src j).dict₂ ()
  xi := fun j => (src j).xi ()
  thAd := fun j => thAdOf R i (tup j) (h j) c0₃ v₀
  Plc := fun j x => ∃ x₀, Place R i (tup j) (h j) c0₃ (jVx R i (tup j) x₀) x

theorem repsR_map {K K' : Type} [Field K] [Field K'] (j : K →+* K') {t : T0} {Cl : Type} {h : Cl → GA D (Vc D i)} {bad J' Lh gam}
    {vol : K} (hr : RepsR R i t h bad J' Lh gam vol) : RepsR R i t h bad J' Lh gam (j vol) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  exact ⟨h1, h2, h3, h4, by rw [h5, map_inv₀, map_natCast], h6⟩

set_option maxHeartbeats 1000000 in

theorem pins_merge {F : Face D A} (hR : R.Char F) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {ι x₀}
    (hsrc : ∀ j, (src j).Pins κ v₀ ι x₀)
    (hlift : ThPinsR R i jL₃ (inC c₃) v₀ c0₃ ι C.Q.l.M (Mfr C.Q.l) lev)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c fun g => (lev g, LinearMap.id))
    (hio : IoLFRec c₃ (fun τ => embF c₃ (tauE D τ)) (lamV D i) (wtA κ) io₃ hw₃)
    (hh : ∀ j, ∃ J', RepsR R i (tup j) (h j) ((src j).bad ()) J' ((src j).Lh ()) ((src j).gam ()) ((src j).vol ()))
    (c0 : ℂ) (hc0 : ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) (cs : J → ℂ) (hu : ∀ j, (u j : ℂ) * cs j = c0)
    (hcs : ∀ j, CXiAt (Wc D i) (rank_Wc i) (inC (src j).c') ((src j).dδ ()) ((src j).U₂ ()) ((src j).dict₂ ()) ι x₀
      ((src j).xi ()) (cs j)) :
    (merge src c₃ h₃ hs jL₃ hV₃ c0₃ lev io₃ hw₃ u h v₀).Pins κ v₀ ι x₀ := by
  have hu0 : ∀ j, u j ≠ 0 := fun j h0 => by
    obtain ⟨m, hm, e⟩ := hc0
    rw [← hu j, h0] at e
    simp [hm.ne'] at e
  refine ⟨hlift, fun j => ⟨?_, ((hsrc j).tuple ()).B, ((hsrc j).tuple ()).xi, ((hsrc j).tuple ()).phi, ((hsrc j).tuple ()).half⟩,
    ⟨hact, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ h₃ _ _ hact).1⟩, fun j => (hsrc j).bad (), fun j => (hsrc j).reps (),
    fun j => ⟨fun k => congrArg (incF _ c₃ (hs j)) (((hsrc j).ep ()).1 k), epIs_map (hs j) ((hsrc j).ep ()).2⟩, hio,
    fun j k q => phiHat_covBC (hs j) _ (u j) _ _ q ((hsrc j).w () k q),
    fun j => covPin_covBC (hs j) _ (hu0 j) ((hsrc j).cov ()), ?_, fun j => (hsrc j).model₂ ()⟩
  · obtain ⟨J', hr⟩ := hh j
    exact ⟨h j, J', repsR_map _ hr, GlobalTheory.RationalValues.placeEx_of_char R F hR i jL₃ (inC c₃) hlift (tup j) (h j),
      thAdIs_thAdOf R i (tup j) (h j) c0₃ hR.models.HV hr.2.2.1 hr.2.2.2.2.2.1 v₀, fun _ => Iff.rfl⟩
  · refine (cXiVal_iff _ _ _ _ _ _ _ _ _).2 ⟨c0, hc0, fun j => ?_⟩
    rw [← hu j]
    exact GlobalTheory.T.unfolding_frame_delta_change D _ _ _ _ _ _ _ _ (hs j) _ _ _ (u j) _ _ _ _ _ _ ((hsrc j).cov ()).1.2.2.2.2.2.2.2.1 (hcs j)

end Merge

end GlobalTheory.OneMapAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianCubeFunction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

section Gens

variable {S : Scheme.{0}} {X : Scheme.{0}} (M : LB X) (T : Over S)

def HasGen (F : ∀ (U : Type) [CommGroup U], ((T.left ⟶ X) → U) → U)
    (f : ∀ (T' : Over S) (_ : T' ⟶ T) (p : T'.left) (_ : (T'.left ⟶ X) → M.ι), (T'.left.presheaf.stalk p)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (T.left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb M φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (T.left ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ (T' : Over S) (σ : T' ⟶ T) (p : T'.left) (J : (T'.left ⟶ X) → M.ι), Good M p J → val t σ.left p J = f T' σ p J

variable {M T}

theorem HasGen.mul {F F' : ∀ (U : Type) [CommGroup U], ((T.left ⟶ X) → U) → U}
    {f f' : ∀ (T' : Over S) (_ : T' ⟶ T) (p : T'.left) (_ : (T'.left ⟶ X) → M.ι), (T'.left.presheaf.stalk p)ˣ}
    (h : HasGen M T F f) (h' : HasGen M T F' f') :
    HasGen M T (fun U _ h => F U h * F' U h) (fun T' σ p J => f T' σ p J * f' T' σ p J) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen M _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => ?_, fun T' σ p J hJ => ?_⟩
  · exact (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (hF U h) (hF' U h))
  · rw [val_mul hJ, hv _ _ _ _ hJ, hv' _ _ _ _ hJ]

theorem HasGen.inv {F : ∀ (U : Type) [CommGroup U], ((T.left ⟶ X) → U) → U}
    {f : ∀ (T' : Over S) (_ : T' ⟶ T) (p : T'.left) (_ : (T'.left ⟶ X) → M.ι), (T'.left.presheaf.stalk p)ˣ}
    (h : HasGen M T F f) :
    HasGen M T (fun U _ h => (F U h)⁻¹) (fun T' σ p J => (f T' σ p J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen M _ _ t, DVR.invGen_isGen _ _ _ _ ht,
    fun U _ h => ?_, fun T' σ p J hJ => ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, hF]
  · rw [val_inv, hv _ _ _ _ hJ]

theorem HasGen.exists_unit (hM : M.IsLB) {F : ∀ (U : Type) [CommGroup U], ((T.left ⟶ X) → U) → U}
    {f : ∀ (T' : Over S) (_ : T' ⟶ T) (p : T'.left) (_ : (T'.left ⟶ X) → M.ι), (T'.left.presheaf.stalk p)ˣ}
    (h : HasGen M T F f) (hF1 : ∀ (U : Type) [CommGroup U] (h : (T.left ⟶ X) → U), F U h = 1) :
    ∃ w : Γ(T.left, ⊤)ˣ, ∀ (T' : Over S) (σ : T' ⟶ T) (p : T'.left) (J : (T'.left ⟶ X) → M.ι), Good M p J →
      gm σ.left p ⊤ w = f T' σ p J := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  obtain ⟨u, -, vu⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => ((hF U h).trans (hF1 U h)).trans (Fintype.prod_empty _).symm) t ht
  have le : (⊤ : T.left.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (T.left ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (u.s PEmpty.elim), fun T' σ z J hJ => (gm_res σ.left z le trivial _).trans
    ((val_of u σ.left z J PEmpty.elim fun k => k.elim).symm.trans ?_)⟩
  rw [vu _ _ z J hJ, hv _ _ _ _ hJ]

theorem range_subset_of_preimage {Z : Scheme.{0}} {V : X.Opens} {ψ : Z ⟶ X} (h : ψ ⁻¹ᵁ V = ⊤) :
    Set.range ψ ⊆ Set.range V.ι := by
  rintro _ ⟨z, rfl⟩
  have : z ∈ ψ ⁻¹ᵁ V := h ▸ trivial
  exact ⟨⟨ψ z, this⟩, rfl⟩

open Classical in

def genVal {V : X.Opens} (g : LB.Gen (M.pull V.ι)) {Z : Scheme.{0}} (p : Z) (J : (Z ⟶ X) → M.ι) (ψ : Z ⟶ X) :
    (Z.presheaf.stalk p)ˣ :=
  if h : ψ ⁻¹ᵁ V = ⊤ then val g (IsOpenImmersion.lift V.ι ψ (range_subset_of_preimage h)) p J else 1

theorem genVal_comp {V : X.Opens} (g : LB.Gen (M.pull V.ι)) {Z : Scheme.{0}} (p : Z) (J : (Z ⟶ X) → M.ι)
    (r : Z ⟶ V.toScheme) : genVal g p J (r ≫ V.ι) = val g r p J := by
  have h : (r ≫ V.ι) ⁻¹ᵁ V = ⊤ := by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]; rfl
  rw [genVal, dif_pos h]
  congr 1
  rw [← cancel_mono V.ι, IsOpenImmersion.lift_fac]

theorem hasGen_genVal {V : X.Opens} (g : LB.Gen (M.pull V.ι)) (hg : g.IsGen) (ψ : T.left ⟶ X) (hψ : ψ ⁻¹ᵁ V = ⊤) :
    HasGen M T (fun _ _ h => h ψ) (fun _ σ p J => genVal g p J (σ.left ≫ ψ)) := by
  obtain ⟨r, rfl⟩ : ∃ r : T.left ⟶ V.toScheme, r ≫ V.ι = ψ :=
    ⟨_, IsOpenImmersion.lift_fac V.ι ψ (range_subset_of_preimage hψ)⟩
  refine ⟨PUnit, inferInstance, _, _, LB.pullGen M _ _ g r, DVR.pullGen_isGen _ _ _ _ hg _,
    fun U _ h => by simp, fun T' σ p J hJ => ?_⟩
  exact (val_pull hJ _ _ _).trans ((genVal_comp g p J _).symm.trans (congrArg (genVal g p J) (Category.assoc _ _ _)))

end Gens

section Cube

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

theorem hasGen_cub {T : Over S} (x x' y : T ⟶ A) :
    HasGen L.L T (fun _ _ h => h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ *
        h x.left * h x'.left * h y.left * (h (1 : T ⟶ A).left)⁻¹)
      (fun _ σ p J => cubV c p J (σ ≫ x) (σ ≫ x') (σ ≫ y)) :=
  ⟨thK, inferInstance, _, _, LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift x (lift x' y)).left,
    DVR.pullGen_isGen _ _ _ _ c.isGen _, fun _ _ h => prod_cub x x' y h, fun _ σ _ _ hJ => val_cub c σ hJ x x' y⟩

def diff₂ {G U : Type} [Mul G] [CommGroup U] (h : G → U) (z b d : G) : U :=
  h (z * b * d) * (h (z * b))⁻¹ * (h (z * d))⁻¹ * h z

def cubeVal {G U : Type} [Mul G] [CommGroup U] (θ : G → G → G → U) (h : G → U) (z a b d : G) : U :=
  θ (z * a) b d * (θ z b d)⁻¹ * (diff₂ h (z * a) b d)⁻¹ * diff₂ h z b d

theorem prod_diff₂ {G U : Type} [CommGroup G] [CommGroup U] (h : G → U) (z b d : G) (k : ℕ) :
    ∏ i ∈ Finset.range k, diff₂ h (z * b ^ i) b d =
      h (z * b ^ k * d) * (h (z * b ^ k))⁻¹ * (h (z * d))⁻¹ * h z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, diff₂, pow_succ b, ← _root_.mul_assoc z]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem prod_cubeVal {G U : Type} [CommGroup G] [CommGroup U] {θ : G → G → G → U} (hθ : IsCub θ) (h : G → U)
    (z b d : G) (k : ℕ) (hb : b ^ k = 1) :
    ∏ i ∈ Finset.range k, cubeVal θ h z (b ^ i) b d = cubN θ k 1 b d * ((θ z b d)⁻¹ * diff₂ h z b d) ^ k := by
  have e := hθ.N_split k z b d
  rw [hb, hθ.face₂, _root_.one_mul] at e
  have e' := prod_diff₂ h z b d k
  rw [hb, _root_.mul_one] at e'
  simp only [cubeVal, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_const, Finset.card_range]
  rw [e', ← e, cubN]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, mul_pow]
  module

theorem cubeVal_quot {G U : Type} [CommGroup G] [CommGroup U] {θ : G → G → G → U} (hθ : IsCub θ) (h : G → U)
    (z x y : G) (k : ℕ) (hx : x ^ k = 1) (hy : y ^ k = 1) :
    (∏ i ∈ Finset.range k, cubeVal θ h z (y ^ i) y x) / ∏ i ∈ Finset.range k, cubeVal θ h z (x ^ i) x y =
      cubN θ k 1 y x * (cubN θ k 1 x y)⁻¹ := by
  have d : diff₂ h z y x = diff₂ h z x y := by
    rw [diff₂, diff₂, mul_right_comm z y x, mul_right_comm (h _)]
  rw [prod_cubeVal hθ h z y x k hy, prod_cubeVal hθ h z x y k hx, hθ.s12 z y x, d, mul_div_mul_right_eq_div,
    div_eq_mul_inv]

variable {V : A.left.Opens} (g : LB.Gen (L.L.pull V.ι)) (hg : g.IsGen)

omit [IsCommMonObj A] in
include hg in
theorem hasGen_diff₂ {T : Over S} (z b d : T ⟶ A) (h₀ : InOpen V z) (h₁ : InOpen V (z * b)) (h₂ : InOpen V (z * d))
    (h₃ : InOpen V (z * b * d)) :
    HasGen L.L T (fun _ _ h => diff₂ (fun q : T ⟶ A => h q.left) z b d)
      (fun T' σ p J => diff₂ (fun q : T' ⟶ A => genVal g p J q.left) (σ ≫ z) (σ ≫ b) (σ ≫ d)) := by
  have := (((hasGen_genVal g hg _ h₃).mul (hasGen_genVal g hg _ h₁).inv).mul (hasGen_genVal g hg _ h₂).inv).mul
    (hasGen_genVal g hg _ h₀)
  simpa only [diff₂, ← Over.comp_left, MonObj.comp_mul] using this

include hg in
theorem exists_cube_unit {T : Over S} (z a b d : T ⟶ A) (h : CubeIn V z a b d) :
    ∃ w : Γ(T.left, ⊤)ˣ, ∀ (T' : Over S) (σ : T' ⟶ T) (p : T'.left) (J : (T'.left ⟶ A.left) → L.L.ι), Good L.L p J →
      gm σ.left p ⊤ w = cubeVal (cubV c p J) (fun q : T' ⟶ A => genVal g p J q.left)
        (σ ≫ z) (σ ≫ a) (σ ≫ b) (σ ≫ d) := by
  have D₁ := hasGen_diff₂ g hg (z * a) b d (by simpa using h 1 0 0) (by simpa using h 1 1 0)
    (by simpa using h 1 0 1) (by simpa using h 1 1 1)
  have D₀ := hasGen_diff₂ g hg z b d (by simpa using h 0 0 0) (by simpa using h 0 1 0)
    (by simpa using h 0 0 1) (by simpa using h 0 1 1)
  obtain ⟨w, hw⟩ := ((((hasGen_cub c (z * a) b d).mul (hasGen_cub c z b d).inv).mul D₁.inv).mul D₀).exists_unit
    L.isLB (fun U _ h => by
      apply Additive.ofMul.injective
      simp only [diff₂, ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  refine ⟨w, fun T' σ p J hJ => ?_⟩
  rw [hw T' σ p J hJ, cubeVal, MonObj.comp_mul]

end Cube

section Main

def unitOf {R : Type} [CommRing R] : Γ(Sp R, ⊤)ˣ →* Rˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom

theorem unitOn_unitOf {R : Type} [CommRing R] (w : Γ(Sp R, ⊤)ˣ) : unitOn (unitOf w) = w :=
  Units.ext ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply w.val)

theorem unitOf_pull {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (w : Γ(Sp R, ⊤)ˣ) :
    (unitOf (pullU (spMap φ) ⊤ w) : R') = φ (unitOf w : R) := by
  have e := congrArg (fun q => q.hom w.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  exact e

theorem hasCubeFn (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)) : HasCubeFn A := by
  classical
  rintro V ⟨g, hg⟩
  have := A.isAb.comm
  have hC : Out.CubeSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.1
  have hG : Out.GlobalFnsSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨⟨c⟩, -⟩ := hC _ A ⟨A.L, r, A.isLB, hr⟩ rfl
  choose w hw using fun (T : Over (Sp C)) (z a b d : T ⟶ A.A) (h : CubeIn V z a b d) =>
    exists_cube_unit c g hg z a b d h
  refine ⟨fun S _ t z a b d => if h : CubeIn V z a b d then unitOf (w _ z a b d h) else 1, ?_, ?_⟩
  · intro S S' _ _ φ t t' z a b d z' a' b' d' hz ha hb hd h
    have ht : spMap φ ≫ t = t' := by
      have e₁ : z.left ≫ A.A.hom = t := Over.w z
      have e₂ : z'.left ≫ A.A.hom = t' := Over.w z'
      rw [← e₁, ← e₂, hz]; rfl
    let σ : (Over.mk t' : Over (Sp C)) ⟶ Over.mk t := Over.homMk (spMap φ) ht
    obtain rfl : z' = σ ≫ z := Over.OverMorphism.ext hz
    obtain rfl : a' = σ ≫ a := Over.OverMorphism.ext ha
    obtain rfl : b' = σ ≫ b := Over.OverMorphism.ext hb
    obtain rfl : d' = σ ≫ d := Over.OverMorphism.ext hd
    have h' : CubeIn V (σ ≫ z) (σ ≫ a) (σ ≫ b) (σ ≫ d) := fun i j k hi hj hk => by
      simpa only [MonObj.comp_mul, MonObj.comp_pow] using (h i j k hi hj hk).comp σ
    have e : w _ _ _ _ _ h' = pullU (spMap φ) ⊤ (w _ z a b d h) := Geo.Tor.unit_ext fun p _ => by
      choose J hJ using fun ψ : Sp S' ⟶ A.A.left => exists_chart A.isLB (ψ p)
      have e₁ := hw _ _ _ _ _ h' _ (𝟙 _) p J hJ
      have e₂ := hw _ _ _ _ _ h _ σ p J hJ
      simp only [Category.id_comp] at e₁
      refine e₁.trans (e₂.symm.trans ?_)
      exact ((gm_pull (𝟙 _) (spMap φ) p ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)).symm
    simp only [dif_pos h, dif_pos h']
    rw [e]
    exact unitOf_pull φ _
  · intro N hN x y z hx hy hV
    have h₁ : ∀ i : ℕ, CubeIn V z (y ^ i) y x := fun i j k l _ _ _ => by
      have := hV l (i * j + k)
      rwa [pow_add, pow_mul, mul_right_comm z, ← _root_.mul_assoc] at this
    have h₂ : ∀ i : ℕ, CubeIn V z (x ^ i) x y := fun i j k l _ _ _ => by
      have := hV (i * j + k) l
      rwa [pow_add, pow_mul, ← _root_.mul_assoc] at this
    simp only [dif_pos (h₁ _), dif_pos (h₂ _)]
    obtain ⟨u, hu⟩ := exists_weil c hx hy
    rw [← map_prod, ← map_prod, ← map_div]
    refine ((HTLat.weilIs_iff hN hx hy _).1 ?_).symm
    rw [unitOn_unitOf]
    refine (Geo.Tor.weilIs_iff c hG A.isAb hx hy hu _).2 (Geo.Tor.unit_ext fun p _ => ?_)
    choose J hJ using fun ψ : Sp C ⟶ A.A.left => exists_chart A.isLB (ψ p)
    have e₁ := hu _ (𝟙 _) p J hJ
    have e₂ := fun a b d h => hw _ z a b d h _ (𝟙 _) p J hJ
    simp only [Category.id_comp] at e₁ e₂
    refine Eq.trans ?_ ((cubeVal_quot (isCub_cubV c (T := Over.mk (𝟙 (Sp C))) (z := p) (J := J) hJ)
      (fun q => genVal g p J q.left) z x y N hx hy).trans e₁.symm)
    rw [map_div, map_prod, map_prod]
    exact congrArg₂ (· / ·) (Finset.prod_congr rfl fun i _ => e₂ _ _ _ _) (Finset.prod_congr rfl fun i _ => e₂ _ _ _ _)

end Main

end GlobalTheory.WeilIntegral
end
end

