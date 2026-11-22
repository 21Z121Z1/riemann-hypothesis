import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0029

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PEdgeB
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma lft_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) :
    lft s ⊆ lft t := by
  intro a ha
  simp only [lft, Finset.mem_toLeft, Finset.mem_map] at ha ⊢
  obtain ⟨u, hu, e⟩ := ha
  exact ⟨u, h hu, e⟩

private lemma rgt_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) :
    rgt s ⊆ rgt t := by
  intro a ha
  simp only [rgt, Finset.mem_toRight, Finset.mem_map] at ha ⊢
  obtain ⟨u, hu, e⟩ := ha
  exact ⟨u, h hu, e⟩

private lemma omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q := by
  refine Submodule.span_mono ?_
  rintro y ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

private lemma wd_empty' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (w : ι → Module.End ℂ E)
    (c : Finset ι → E) : wd w c ∅ = 0 := by
  simp [wd]

private lemma acx_C' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] {A : Finset ι → Submodule ℂ E}
    {w : ι → Module.End ℂ E} {n : ℤ} {c : Finset ι → E} :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule ℂ E) :=
  ⟨fun h s => h s trivial, fun h s _ => h s⟩

private lemma cech_C' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] {A : Finset ι → Submodule ℂ E}
    {n : ℤ} {c : Finset ι → E} :
    c ∈ (cech A).C n ↔ ∀ s, c s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥ : Submodule ℂ E) :=
  ⟨fun h s => h s trivial, fun h s _ => h s⟩

theorem UpperTheory.Gal.productCup_of_system.edgeB_of :
    EdgeInj → RowEx → L1 → RYBasic → WdUni → WdBasic → EdgeB := by
  intro hEI hRow hL1 hRY hU hW
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h0 y hy hB
  obtain ⟨hRI, hGood, hRmono, -, -⟩ := hRY F K K' d x j2 h0
  have lu : ∀ I J : Finset (Fin (d + 1)), lft (uni I J) = I := fun I J =>
    (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) I J).2.1
  have ru : ∀ I J : Finset (Fin (d + 1)), rgt (uni I J) = J := fun I J =>
    (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) I J).2.2.1
  have cu : ∀ I J : Finset (Fin (d + 1)), (uni I J).card = I.card + J.card := fun I J =>
    (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) I J).2.2.2.1
  let G : Finset (Two d) → Submodule ℂ (DR ℂ K') := fun s => omB ℂ K' (RY (xv x) j2 (lft s) (rgt s)) d
  have hGm : ∀ I J, G (uni I J) = omB ℂ K' (RY (xv x) j2 I J) d := by
    intro I J
    simp only [G, lu, ru]
  have hG0 : ∀ I, G (uni I ∅) = omB ℂ K' (rB ℂ K' (xv x) I) d := by
    intro I
    rw [hGm, hRI]
  have hcech : (fun I => G (uni I ∅)) = fun I => omB ℂ K' (rB ℂ K' (xv x) I) d := funext hG0
  have hmix : (fun I J => G (uni I J)) = fun I J => omB ℂ K' (RY (xv x) j2 I J) d :=
    funext fun I => funext fun J => hGm I J
  obtain ⟨γ, hγ, hγ0, hγI⟩ := hEI (Fin (d + 1)) (DR ℂ K') G d y
    (by rw [hcech]; exact hy) (by rw [hmix]; exact hB)
  let A : Finset (Two d) → Submodule ℂ (DR ℂ K') := fun s => if (lft s).Nonempty then G s else ⊥
  have hAn : ∀ s, (lft s).Nonempty → A s = G s := fun s hs => if_pos hs
  have hAe : ∀ s, ¬ (lft s).Nonempty → A s = ⊥ := fun s hs => if_neg hs
  have hWOk : WOk A (fun _ => 1) := by
    refine ⟨fun _ _ => Commute.one_left _, ?_⟩
    intro s i _ m hm
    by_cases hs : (lft s).Nonempty
    · have hsub : s ⊆ insert i s := Finset.subset_insert _ _
      have hs' : (lft (insert i s)).Nonempty := hs.mono (lft_mono' hsub)
      rw [hAn _ hs] at hm
      show m ∈ A (insert i s)
      rw [hAn _ hs']
      exact omB_mono' (hRmono _ _ _ _ (lft_mono' hsub) (rgt_mono' hsub)) d hm
    · rw [hAe _ hs, Submodule.mem_bot] at hm
      show m ∈ A (insert i s)
      rw [hm]
      exact Submodule.zero_mem _
  have hKE : ∀ b, KE (colA A (fun _ => 1) b) ((d : ℤ) + 2) := by
    intro b m _
    by_cases hb : b.Nonempty
    · have e : (fun L => A (uni b L)) = fun J => omB ℂ K' (RY (xv x) j2 b J) d := by
        funext L
        rw [hAn _ (by rw [lu]; exact hb), hGm]
      show (acx (fun L => A (uni b L)) fun _ => 1).Z m ≤ (acx (fun L => A (uni b L)) fun _ => 1).B m
      rw [e]
      exact hRow F K K' d x j2 h0 d b hb m
    · intro c hc
      have hc0 : c = 0 := by
        funext L
        have h1 := acx_C'.1 hc.1 L
        have hA : A (uni b L) = ⊥ := hAe _ (by rw [lu]; exact hb)
        have h2 : c L ∈ (⊥ : Submodule ℂ (DR ℂ K')) := by
          simp only [hA, ite_self] at h1
          exact h1
        exact (Submodule.mem_bot ℂ).1 h2
      rw [hc0]
      exact Submodule.zero_mem _
  have hdelta : ∀ c : Finset (Two d) → DR ℂ K', wd (fun _ => (1 : Module.End ℂ (DR ℂ K'))) c = deltaL ℂ _ _ c :=
    (hW (Two d) (DR ℂ K') A (fun _ => 1)).2.2.2.2.1
  have hdelta' : ∀ c : Finset (Fin (d + 1)) → DR ℂ K', wd (fun _ => (1 : Module.End ℂ (DR ℂ K'))) c = deltaL ℂ _ _ c :=
    (hW (Fin (d + 1)) (DR ℂ K') (fun _ => ⊥) (fun _ => 1)).2.2.2.2.1
  have hγZ : γ ∈ (acx A fun _ => 1).Z ((d : ℤ) + 1) := by
    refine ⟨?_, ?_⟩
    · refine acx_C'.2 fun s => ?_
      have h1 := cech_C'.1 hγ.1 s
      by_cases hc : (s.card : ℤ) = (d : ℤ) + 1
      · rw [if_pos hc]
        by_cases hs : (lft s).Nonempty
        · rw [hAn _ hs]
          have hne : s.Nonempty := by
            rw [← Finset.card_pos]
            omega
          rw [if_pos ⟨hne, hc⟩] at h1
          exact h1
        · rw [hAe _ hs, Submodule.mem_bot]
          have hl : lft s = ∅ := Finset.not_nonempty_iff_eq_empty.1 hs
          have := hγ0 (rgt s)
          rwa [← hl, (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) ∅ ∅).2.2.2.2 s] at this
      · rw [if_neg hc]
        rw [if_neg (fun h => hc h.2)] at h1
        exact h1
    · show wd _ γ = 0
      rw [hdelta]
      exact hγ.2
  have hBγ : γ ∈ (acx A fun _ => 1).B ((d : ℤ) + 1) := by
    refine hL1 (Fin (d + 1)) (Fin (d + 1)) (DR ℂ K') A (fun _ => 1) ((d : ℤ) + 2) ((d : ℤ) + 1) hWOk hKE γ hγZ ?_ ?_
    · intro b L hL
      exfalso
      have : L.card ≤ d + 1 := by simpa using Finset.card_le_univ L
      omega
    · intro b hb
      exfalso
      have : (0 : ℤ) ≤ b.card := by positivity
      omega
  obtain ⟨η, hη, he⟩ := hBγ
  refine Submodule.mem_map.2 ⟨fun b => η (uni b ∅), ?_, ?_⟩
  · refine cech_C'.2 fun b => ?_
    have h1 := acx_C'.1 hη (uni b ∅)
    rw [cu] at h1
    simp only [Finset.card_empty, add_zero] at h1
    by_cases hb : b.Nonempty ∧ (b.card : ℤ) = (d : ℤ) - 1 + 1
    · rw [if_pos hb]
      have hc : (b.card : ℤ) = (d : ℤ) + 1 - 1 := by omega
      rw [if_pos hc, hAn _ (by rw [lu]; exact hb.1), hG0] at h1
      exact h1
    · rw [if_neg hb]
      by_cases hc : (b.card : ℤ) = (d : ℤ) + 1 - 1
      · have hne : ¬ b.Nonempty := fun h => hb ⟨h, by omega⟩
        rw [if_pos hc, hAe _ (by rw [lu]; exact hne)] at h1
        exact h1
      · rw [if_neg hc] at h1
        exact h1
  · funext I
    have e1 := (hU _ _ (DR ℂ K') (fun _ => 1) η I ∅).1
    rw [wd_empty', smul_zero, add_zero] at e1
    have e2 : wd (fun _ => (1 : Module.End ℂ (DR ℂ K'))) η = γ := he
    rw [e2, hγI] at e1
    rw [e1]
    exact (congrFun (hdelta' _) I).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PIdVal
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section Vals
variable {L : Type} [Field L] [Algebra ℂ L] {B : Subalgebra ℂ L} {e : B →ₐ[ℂ] ℂ}

private lemma val_mul (hV : ValBasic) {v v' : L} {c c' : ℂ} (h : Val B e v c) (h' : Val B e v' c') :
    Val B e (v * v') (c * c') := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨p, rfl⟩ := (hev _ _).1 h
  obtain ⟨p', rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨mul_mem p p', map_mul ev ⟨v, p⟩ ⟨v', p'⟩⟩

private lemma val_add (hV : ValBasic) {v v' : L} {c c' : ℂ} (h : Val B e v c) (h' : Val B e v' c') :
    Val B e (v + v') (c + c') := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨p, rfl⟩ := (hev _ _).1 h
  obtain ⟨p', rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨add_mem p p', map_add ev ⟨v, p⟩ ⟨v', p'⟩⟩

private lemma val_zero (hV : ValBasic) : Val B e (0 : L) 0 := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  exact (hev _ _).2 ⟨zero_mem _, map_zero ev⟩

private lemma val_sum (hV : ValBasic) {ι : Type} (s : Finset ι) (f : ι → L) (c : ι → ℂ)
    (h : ∀ i ∈ s, Val B e (f i) (c i)) : Val B e (∑ i ∈ s, f i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_zero hV
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact val_add hV (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma val_unique (hV : ValBasic) {v : L} {c c' : ℂ} (h : Val B e v c) (h' : Val B e v c') :
    c = c' := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨p, rfl⟩ := (hev _ _).1 h
  obtain ⟨p', rfl⟩ := (hev _ _).1 h'
  rfl

private lemma val_of_mem (hV : ValBasic) {v : L} (h : v ∈ loc B e) : ∃ c, Val B e v c := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  exact ⟨_, (hev _ _).2 ⟨h, rfl⟩⟩

end Vals

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private lemma muP_tmul (τ : DR ℂ K →ₗ[K] K) (w' w'' w : DR ℂ K) :
    muP F K τ (w' ⊗ₜ w'') w = (Algebra.trace F K (τ (w' * w))) ⊗ₜ[ℂ] w'' := by
  simp [muP]

private lemma mulP_tmul (f : F) (w : DR ℂ K) : mulP F K (f ⊗ₜ w) = algebraMap F K f • w := by
  simp [mulP]

private lemma acts_expand (τ : DR ℂ K →ₗ[K] K) {m : ℕ} (w' w : Fin m → DR ℂ K) (v : DR ℂ K) :
    mulP F K (muP F K τ (∑ k, w' k ⊗ₜ w k) v) =
      ∑ k, algebraMap F K (Algebra.trace F K (τ (w' k * v))) • w k := by
  simp only [map_sum, LinearMap.sum_apply, muP_tmul, mulP_tmul]

private lemma omG_ne {d : ℕ} (x : Fin (d + 1) → Fˣ) : algebraMap F K (omG x 0) ≠ 0 := by
  refine (map_ne_zero _).2 ?_
  exact Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (x l).ne_zero (x 0).ne_zero

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.idVal_of :
    LocForms → DtBasic → CRT → TrVal → ResVal → LatA → ValBasic → OmLoc → IdVal := by
  intro hLF hDt hCRT hTV hRV hLat hV hOL F K _ _ _ _ _ _ d x cov τ hτ red a ha m w' w hw hact z
  classical
  obtain ⟨hli, hdt, hvol, -, -⟩ := hDt F K d x cov τ hτ
  set B := rB ℂ K (xv x) ({0} : Finset (Fin (d + 1))) with hB
  set om : K := algebraMap F K (omG x 0) with hom
  have omne : om ≠ 0 := omG_ne x
  have hτv : τ (dtS K x Finset.univ) = om := by
    rw [hvol, map_smul, hτ.1, smul_eq_mul, mul_one]
  have hgEq : ∀ y ∈ omB ℂ K B d, y = (τ y / om) • dtS K x Finset.univ := by
    intro y hy
    have h1 := (GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K d (xv x) cov).2 τ hτ y (mem_deg_of_mem_omB B d y hy)
    rw [hvol, smul_smul, div_mul_cancel₀ _ omne]
    exact h1
  have hgLoc : ∀ (e : fib ℂ K (xv x)), ∀ y ∈ omB ℂ K B d, τ y / om ∈ loc B e.1 := by
    intro e y hy
    have hle : B ≤ loc B e.1 := (hV K B e.1).1
    have hy' := (hOL K B e.1 d).2.2 _ hle hy
    obtain ⟨c, hc, hce⟩ := (hLF F K d x cov red e d y).1 hy'
    have hp : Finset.univ.powersetCard d = ({Finset.univ} : Finset (Finset (Fin d))) := by
      have := Finset.powersetCard_self (Finset.univ : Finset (Fin d))
      simpa using this
    rw [hp, Finset.sum_singleton] at hce
    have : τ y = c Finset.univ * om := by
      rw [hce, map_smul, hτv, smul_eq_mul]
    rw [this, mul_div_cancel_right₀ _ omne]
    exact hc _
  have hyB : ∀ k (S : Finset (Fin d)), S.card = a → w' k * dtS K x S ∈ omB ℂ K B d := by
    intro k S hS
    have := mul_mem_omB B (d - a) a _ (hw k).1 _ (hS ▸ hdt S)
    rwa [Nat.sub_add_cancel ha] at this
  have hwL : ∀ k, ∃ c : Finset (Fin d) → K, (∀ S, c S ∈ loc B z.1) ∧
      w k = ∑ S ∈ Finset.univ.powersetCard a, c S • dtS K x S := fun k =>
    (hLF F K d x cov red z a (w k)).1 ((hOL K B z.1 a).2.2 _ (hV K B z.1).1 (hw k).2)
  choose b hbl hbe using hwL
  have hφ : ∀ v : K, ∃ c : ℂ, v ∈ loc B z.1 → Val B z.1 v c := by
    intro v
    by_cases hv : v ∈ loc B z.1
    · obtain ⟨c, hc⟩ := val_of_mem hV hv
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose φ hφ using hφ
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_laurentConstantTermForm_functionField ℂ F d (xv x) cov.pd
  refine ⟨fun k S => τ (w' k * dtS K x S) / om, b, fun k S => φ (τ (w' k * dtS K x S) / om),
    fun k T => φ (b k T), fun k S hS => hgEq _ (hyB k S hS), hbe, fun k S hS =>
      ⟨hφ _ (hgLoc z _ (hyB k S hS)), hφ _ (hbl k S)⟩, ?_⟩
  intro S T hS hT
  obtain ⟨h, hh⟩ := (hCRT F K d x cov).2 (fun e => if e = z then 1 else 0)
  set g : Fin m → K := fun k => τ (w' k * dtS K x S) / om with hg
  set t : Fin m → F := fun k => Algebra.trace F K (g k * h) with ht
  have hgy : ∀ k, τ (w' k * dtS K x S) = om * g k := by
    intro k
    simp only [hg]
    field_simp
  have htr : ∀ k, Algebra.trace F K (om * (g k * h)) = omG x 0 * t k := by
    intro k
    rw [hom, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have claim1 : ∀ k, t k ∈ rA ℂ (xv x) {0} := by
    intro k
    have h1 := (GlobalTheory.T.complementaryModule_standardOpens_iff ℂ F K d (xv x) cov τ hτ {0} ⟨0, by simp⟩ (om * (g k * h))).2
      ⟨(h : K) • (w' k * dtS K x S), smul_mem_omB B d _ h.2 _ (hyB k S hS), by
        rw [map_smul, hgy, smul_eq_mul]; ring⟩ 1 (Subalgebra.one_mem _)
    rw [mul_one, htr] at h1
    have h2 := ((hLat F d x cov.pd {0} 0 (by simp)).2.1 _).1 h1
    have hne : omG x 0 ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (x l).ne_zero (x 0).ne_zero
    rwa [mul_div_cancel_left₀ _ hne] at h2
  have claim2 : ∀ k, Val B z.1 (algebraMap F K (t k)) (φ (g k)) := by
    intro k
    have hres := hRV F K d x cov ρ hρ z (t k) (claim1 k)
    have hγ0 : ∀ e : fib ℂ K (xv x), ∃ c, Val B e.1 (g k) c := fun e =>
      val_of_mem hV (hgLoc e _ (hyB k S hS))
    choose γ0 hγ0 using hγ0
    have hγ : ∀ e : fib ℂ K (xv x), Val B e.1 (g k * h) (γ0 e * e.1 h) := fun e =>
      val_mul hV (hγ0 e) ((hV K B e.1).2.2.1 h)
    have htv := hTV F K d x cov red ρ hρ (g k * h) (fun e => γ0 e * e.1 h) hγ (claim1 k)
    have hfs : ∑ᶠ e, γ0 e * e.1 h = φ (g k) := by
      rw [finsum_eq_single _ z]
      · rw [hh z]
        simp only [if_true, mul_one]
        exact val_unique hV (hγ0 z) (hφ _ (hgLoc z _ (hyB k S hS)))
      · intro e he
        rw [hh e, if_neg he, mul_zero]
    have : ρ (t k) = φ (g k) := by rw [← hfs]; exact htv
    rwa [this] at hres
  have claim3 : ∑ k, algebraMap F K (t k) • w k = (h : K) • dtS K x S := by
    have h1 := hact ((h : K) • dtS K x S)
      (Submodule.smul_mem _ _ (hS ▸ mem_deg_of_mem_omB B _ _ (hdt S)))
    rw [acts_expand] at h1
    have h2 : ∀ k, algebraMap F K (Algebra.trace F K (τ (w' k * ((h : K) • dtS K x S)))) • w k =
        om • (algebraMap F K (t k) • w k) := by
      intro k
      rw [mul_smul_comm, map_smul, hgy, smul_eq_mul,
        show (h : K) * (om * g k) = om * (g k * h) by ring, htr, map_mul, mul_smul]
    simp only [h2, ← Finset.smul_sum] at h1
    exact smul_right_injective _ omne h1
  have claim4 : ∀ T ∈ Finset.univ.powersetCard a,
      ∑ k, algebraMap F K (t k) * b k T = if S = T then (h : K) else 0 := by
    have hsum : ∑ T ∈ Finset.univ.powersetCard a,
        ((∑ k, algebraMap F K (t k) * b k T) - if S = T then (h : K) else 0) • dtS K x T = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, ← hbe]
      rw [claim3, Finset.sum_ite_eq, if_pos (by simp [Finset.mem_powersetCard, hS]), sub_self]
    intro T hT
    exact sub_eq_zero.1 (linearIndependent_iff'.1 hli _ _ hsum T hT)
  have hTm : T ∈ Finset.univ.powersetCard a := by simp [Finset.mem_powersetCard, hT]
  have hL : Val B z.1 (∑ k, algebraMap F K (t k) * b k T) (∑ k, φ (g k) * φ (b k T)) :=
    val_sum hV _ _ _ fun k _ => val_mul hV (claim2 k) (hφ _ (hbl k T))
  rw [claim4 T hTm] at hL
  have hz1 : Val B z.1 (h : K) 1 := by
    have := (hV K B z.1).2.2.1 h
    rwa [hh z, if_pos rfl] at this
  by_cases hST : S = T
  · rw [if_pos hST] at hL ⊢
    exact val_unique hV hL hz1
  · rw [if_neg hST] at hL ⊢
    exact val_unique hV hL (val_zero hV)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocForms
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section LocFormsAux

private def Hs {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [Module L V]
    (B : Subalgebra ℂ L) (P : Finset ι) (g : ι → V) (w : V) : Prop :=
  ∃ c : ι → L, (∀ S, c S ∈ B) ∧ w = ∑ S ∈ P, c S • g S

variable {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [Module L V]
  {B : Subalgebra ℂ L} {P : Finset ι} {g : ι → V}

private lemma Hs_zero : Hs B P g 0 := ⟨fun _ => 0, fun _ => B.zero_mem, by simp⟩

private lemma Hs_add {w w' : V} (h : Hs B P g w) (h' : Hs B P g w') : Hs B P g (w + w') := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  exact ⟨fun S => c S + c' S, fun S => B.add_mem (hc S) (hc' S), by
    simp [add_smul, Finset.sum_add_distrib]⟩

private lemma Hs_smul {b : L} (hb : b ∈ B) {w : V} (h : Hs B P g w) : Hs B P g (b • w) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun S => b * c S, fun S => B.mul_mem hb (hc S), by
    simp [Finset.smul_sum, mul_smul]⟩

private lemma Hs_single [DecidableEq ι] {S : ι} (hS : S ∈ P) : Hs B P g (g S) :=
  ⟨fun T => if T = S then 1 else 0, fun T => by dsimp only; split_ifs <;> simp [B.one_mem, B.zero_mem], by
    simp [ite_smul, Finset.sum_ite_eq', hS]⟩

private lemma Hs_sum {α : Type} (s : Finset α) (f : α → V) (h : ∀ a ∈ s, Hs B P g (f a)) :
    Hs B P g (∑ a ∈ s, f a) :=
  _root_.UpperTheory.Reformulated.B.Qh70.Hs_sum s f h

private lemma alt_sorted {V : Type} [AddCommGroup V] [Module L V] {d : ℕ} (t : Fin d → V)
    (S : Finset (Fin d)) (f : Fin S.card → Fin d) (hf : Function.Injective f)
    (hS : ∀ a, f a ∈ S) :
    ∃ n : ℤ, ExteriorAlgebra.ιMulti L S.card (fun a => t (f a)) =
      (n : L) • ExteriorAlgebra.ιMulti L S.card (fun a => t (S.orderEmbOfFin rfl a)) := by
  set σ := Tuple.sort f
  have hs : StrictMono (f ∘ σ) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
  have hu : f ∘ σ = S.orderEmbOfFin rfl :=
    Finset.orderEmbOfFin_unique rfl (fun a => hS _) hs
  have hp := (ExteriorAlgebra.ιMulti L S.card (M := V)).map_perm (fun a => t (f a)) σ
  have hv : ((fun a => t (f a)) ∘ σ) = fun a => t (S.orderEmbOfFin rfl a) := by
    funext a
    simpa using congrArg t (congrFun hu a)
  rw [hv] at hp
  refine ⟨((Equiv.Perm.sign σ : ℤˣ) : ℤ), ?_⟩
  rw [hp, Int.cast_smul_eq_zsmul, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]

private lemma alt_expand {V : Type} [AddCommGroup V] [Module L V] {q d : ℕ} (t : Fin d → V)
    (c : Fin q → Fin d → L) :
    ExteriorAlgebra.ιMulti L q (fun j => ∑ l, c j l • t l) =
      ∑ f : Fin q → Fin d, (∏ j, c j (f j)) • ExteriorAlgebra.ιMulti L q (fun j => t (f j)) := by
  have h := (ExteriorAlgebra.ιMulti L q (M := V)).toMultilinearMap.map_sum
    (fun j l => c j l • t l)
  simp only [AlternatingMap.coe_multilinearMap] at h
  rw [h]
  refine Finset.sum_congr rfl fun f _ => ?_
  exact (ExteriorAlgebra.ιMulti L q (M := V)).toMultilinearMap.map_smul_univ _ _

end LocFormsAux

theorem UpperTheory.Gal.productCup_of_system.locForms_of :
    LocOne → LocForms := by
  intro hone F L _ _ _ _ _ _ d x hfc hr e q w
  have ht : ∀ j, tt L x j ∈ loc (rB ℂ L (xv x) {0}) e.1 := fun j =>
    ⟨1, by simp, by simpa [tt] using tco_mem ℂ L (xv x) j⟩
  constructor
  · intro hw
    change Hs _ _ _ w
    refine Submodule.span_induction ?_ Hs_zero (fun _ _ _ _ => Hs_add) ?_ hw
    · rintro _ ⟨b, hb, v, hv, rfl⟩
      refine Hs_smul hb ?_
      choose c hcB hcD using fun j => hone F L d x hfc hr e (v j) (hv j)
      simp only [hcD]
      rw [alt_expand]
      refine Hs_sum _ _ fun f _ => Hs_smul (Subalgebra.prod_mem _ fun j _ => hcB j _) ?_
      by_cases hf : Function.Injective f
      · obtain ⟨S, hS⟩ : ∃ S, S = Finset.univ.image f := ⟨_, rfl⟩
        have hcard : S.card = q := by
          rw [hS, Finset.card_image_of_injective _ hf]; simp
        subst hcard
        obtain ⟨n, hn⟩ := alt_sorted (L := L) (fun l => D ℂ L (tt L x l)) S f hf
          (fun a => by simp [hS])
        rw [hn]
        exact Hs_smul (intCast_mem _ n) (Hs_single (g := dtS L x) (by simp))
      · have : ¬ Function.Injective (fun j => D ℂ L (tt L x (f j))) := fun h =>
          hf fun a b hab => h (by simp [hab])
        rw [AlternatingMap.map_eq_zero_of_not_injective _ _ this]
        exact Hs_zero
    · intro a w _ h
      rw [← algebraMap_smul L a w]
      exact Hs_smul (Subalgebra.algebraMap_mem _ a) h
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun S hS => ?_
    have hcard := (Finset.mem_powersetCard.1 hS).2
    subst hcard
    exact Submodule.subset_span ⟨c S, hc S, fun a => tt L x (S.orderEmbOfFin rfl a),
      fun j => ht _, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PMinorSum
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem det_submatrix_orderEmbOfFin_eq_subtype {R : Type*} [CommRing R] {d k : ℕ}
    (B : Matrix (Fin d) (Fin d) R) (s : Finset (Fin d)) (h : s.card = k) :
    (B.submatrix (s.orderEmbOfFin h) (s.orderEmbOfFin h)).det =
      (B.submatrix (Subtype.val : s → Fin d) Subtype.val).det := by
  rw [← Matrix.det_submatrix_equiv_self (s.orderIsoOfFin h).toEquiv
    (B.submatrix (Subtype.val : s → Fin d) Subtype.val)]
  rfl

theorem UpperTheory.Gal.productCup_of_system.minorSum_of :
    MinorSum := by
  intro d a A
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  exact (det_submatrix_orderEmbOfFin_eq_subtype A S _).symm
end

