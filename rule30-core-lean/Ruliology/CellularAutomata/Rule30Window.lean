module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# A kernel-checked window for Problem 1

The center column of rule 30 has no eventual period `P ≤ N/4` with transient `≤ N/2`, for
`N = windowN`: every such `P` has a witness `t` in `[N/2, N/2 + 32)` with `c(t) ≠ c(t + P)`
(`no_small_eventual_period`).

The center bits are computed in the kernel. A row of rule 30 is packed into a natural number,
bit `k` holding the cell at position `k − K`, so one step is three bitwise operations
(`stepRow`); `row_testBit` proves the packed rows equal `cell`. `centerLoop` scans `N` steps and
records bit `K` of each row, and `centerLoop_spec` proves what it records.

This is a finite check, far smaller than the published billion-bit computations; its point is
that every step, including the simulation, is checked by Lean's kernel.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Window

open Rule30Jen Rule30Prize

/-- One rule-30 step on a packed row: bit `k` becomes `left xor (center or right)`. -/
def stepRow (r : Nat) : Nat := (r <<< 1) ^^^ (r ||| (r >>> 1))

/-- The packed row at time `t`, seeded at bit `K`. -/
def row (K : Nat) : Nat → Nat
  | 0 => 2 ^ K
  | t + 1 => stepRow (row K t)

theorem cell_congr' {t : Nat} {p q : Int} (h : p = q) : cell t p = cell t q := h ▸ rfl

/-- **The packed rows are rule 30**: while `t ≤ K`, bit `k` of the row is the cell at `k − K`. -/
theorem row_testBit (K : Nat) : ∀ t, t ≤ K → ∀ k : Nat, (row K t).testBit k = cell t ((k : Int) - K)
  | 0, _, k => by
    simp only [row, Nat.testBit_two_pow, cell]
    by_cases h : K = k
    · subst h; simp
    · rw [decide_eq_false h, decide_eq_false (by omega)]
  | t + 1, ht, k => by
    have ih := row_testBit K t (by omega)
    have e : cell (t + 1) ((k : Int) - K) = rule (cell t ((k : Int) - K - 1))
        (cell t ((k : Int) - K)) (cell t ((k : Int) - K + 1)) := rfl
    rw [e]
    simp only [row, stepRow, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, rule]
    rw [ih k, ih (1 + k), cell_congr' (show ((1 + k : Nat) : Int) - K = (k : Int) - K + 1 by omega)]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [cell_eq_false_of_lt t ((((0 : Nat) : Int)) - K - 1) (by omega)]
      simp
    · rw [show decide (k ≥ 1) = true from decide_eq_true hk, Bool.true_and, ih (k - 1),
        cell_congr' (show ((k - 1 : Nat) : Int) - K = (k : Int) - K - 1 by omega)]

/-- Scan `n` steps from row `r` at time `t`, recording bit `K` of each row at bit `t` of `acc`.
The `Nat.ble 0` tests are always true; they make the kernel evaluate each value as it goes. -/
def centerLoop (K : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, t, r, acc =>
    if (Nat.ble 0 (if r.testBit K then acc ||| (1 <<< t) else acc) && Nat.ble 0 (stepRow r)) = true
    then centerLoop K n (t + 1) (stepRow r) (if r.testBit K then acc ||| (1 <<< t) else acc)
    else 0

theorem centerLoop_succ (K n t r acc : Nat) :
    centerLoop K (n + 1) t r acc =
      centerLoop K n (t + 1) (stepRow r) (if r.testBit K then acc ||| (1 <<< t) else acc) := by
  rw [centerLoop, Nat.ble_eq_true_of_le (Nat.zero_le _), Nat.ble_eq_true_of_le (Nat.zero_le _)]
  rfl

/-- What `centerLoop` records: bit `i` of the result is the center bit of row `i`. -/
theorem centerLoop_spec (K : Nat) : ∀ n t acc, (∀ i, t ≤ i → acc.testBit i = false) → ∀ i,
    (centerLoop K n t (row K t) acc).testBit i =
      if i < t then acc.testBit i else if i < t + n then (row K i).testBit K else false := by
  intro n
  induction n with
  | zero =>
    intro t acc hacc i
    simp only [centerLoop, Nat.add_zero]
    by_cases h : i < t
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, hacc i (by omega)]
  | succ n ih =>
    intro t acc hacc i
    have hbit : ∀ j, (if (row K t).testBit K then acc ||| (1 <<< t) else acc).testBit j =
        (acc.testBit j || (decide (t = j) && (row K t).testBit K)) := by
      intro j
      cases (row K t).testBit K
      · simp
      · simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    rw [centerLoop_succ, show stepRow (row K t) = row K (t + 1) from rfl,
      ih (t + 1) _ (by
        intro j hj
        rw [hbit j, hacc j (by omega), decide_eq_false (show ¬ t = j by omega)]
        rfl),
      hbit i]
    by_cases h1 : i < t
    · rw [ite_eq_left (show i < t + 1 by omega), ite_eq_left h1, decide_eq_false (show ¬ t = i by omega),
        Bool.false_and, Bool.or_false]
    · by_cases h2 : i = t
      · rw [ite_eq_left (show i < t + 1 by omega), ite_eq_right h1, ite_eq_left (show i < t + (n + 1) by omega),
          hacc i (by omega), decide_eq_true h2.symm, Bool.true_and, Bool.false_or, h2]
      · rw [ite_eq_right (show ¬ i < t + 1 by omega), ite_eq_right h1, show t + 1 + n = t + (n + 1) by omega]

/-! ### The window -/

/-- The window size. -/
def windowN : Nat := 16384

/-- The center bits `c(0), …, c(windowN − 1)`, bit `t` being `c(t)`. -/
def centerBits : Nat := 303483238097394502718749854119478324825170836741319777851815077088114433281144542755341813346623659790982348088530996452127370521535195714520520652876060548735477989118352055640335704753205164342056219528595284398195955693984831478516366735379565126443572229624457780205345493066801180337570816236036802465875911620705085006632883161268634873928257600610090151394039891313123787725116684366517338477268760364365813083885293713960735317022346977474351978489827648279979683671393633142762891947880367372087976014810162607306816406320333773414733409725466784702904614560330535304165477283479512323997437748142458628125143148106890323455107597834031843608364737865212985149628428809165493223817532751731711602712536205090506561699681335440379478314749426273665219463433366831420389727387979621556494279829901357413262255054972424051345628245296448009226156750051732005015013271040400139292828641507613469363682025224559001486425451798765487527729774341653979416409114283138717775234300671089913203344663595935397040818458336685891919519273693614303698892693184438388853013024564779881053759757099856081604746931138068412948448492155254677709642238077252203105338759747161151169816285249609304315074723584248684114942093728182514010683064458899195877572597714710826641712997775581994908043756011527274017882902795890728844857823257545586766818766724274443061085956771315846447437967606569870277902415593027397040370831861057498271077590858570047166627908296156314303036129548948757605592573721073309697369934982990639462077369092697110628109136940189520154206709728118718675124017772086543577179928515515497411428082791461547067367223722415805955549161926216963911535346331325161935286558565613640575992003428819932423336193189069823814094158597408083275572686614923755991179993944011238435561632942680667226620755272792575667086456149066733281603488649100339239897449828009831409172818988748819130282207757564979637499030942638007729475046168829865760609566371713497871947161736150983165507209835483118745295198583312071243763795901704850672955511636013876338161419503565432846828480835104848849889531481129088643498830480563562038628213085887213284327797969022459604600201550586821752749901041353954604959400470979593122807677919467017508312319909239350714594103488243193708917012095529320897060125097703021954051344437517335245591207992326126178626660480687899064774390810436425213561834493699658600357430218384073496433512794757209325842325564727448831663060188040495302356014465825191826192529864051852143455738582252219684661952266030491742926381424164344431370036691397005934314299509310535092553163173872305110235871415587249046592171301420474766606613419945229696078638814625157870576131388760138757527026440291581597899015129135941989286105658883266342564506861041387875843351579883862352957999239216206412106909774844032181322618594766986085872954911344950748904194163568725786696960087742180013491880783536590701702518491491216702309359075961809138326571598701108875401242585912687916057259083119505295490645451836213537856318814391081884863159356663249208867920453059291161892124111395491499550075412218233298804107854192295424576133311771011523481284872584202979554266070661423706801241767837039954763380220626702714613439359202214377015621846343550045759883586622528626979158921017364466569589616789673235303774572061359198535129516668878927014522623745116631732522310072675116517317420452531713923949453711451823166199317026338009457779325437118296573899194854035172172128907227366310601097644657694735862899649775610769616677438445027342957537396590091272338448080558735063664085487414930172739062071369111595254320852323289165986187701295901477070654248151453211654862345673004722814614187816500122539116800401239458466897971114081955409834583613173259401575313080065494856074261758170676173332782393525093495277806856545729402701913738065360801881522793721692360766056932960228514939866869505584409742824607025137326321602477183173135697081507244480343616876886521958518748438475497270694596032145131242410705211989964089875330451036075656662812657720583399925828600971572457250044116076706702934718764064978230444855891074309886179330692974769146224118599048537597079244595854138227480350648182507279826260311085347476239602141670931820506721548199269663072464775845835270246369512335097111744108731570893918942903272622092826380189641862523521433803431410708054522554235775262782919345594579766235104274106717500879815842049184272969705404845175433772381218228763408777216209999550938268451145547928867761931518938056223654104829351737418150181546803847491501577084068333661092444474040328647295466768012649627481872069755137495621931086609906401292212620088346243583258621771050461649583754983912363224144342410008581648959734323149149840150972044713254218679624332949914484262748813775995623747421941524528609067271060075035397595777078545294463722609378800823160012551253284636517836234297578091838692946084471611

theorem centerLoop_eq : centerLoop windowN windowN 0 (2 ^ windowN) 0 = centerBits := by
  decide +kernel

theorem center_eq_bit (t : Nat) (ht : t < windowN) : center t = centerBits.testBit t := by
  have h := centerLoop_spec windowN windowN 0 0 (by simp) t
  rw [show row windowN 0 = 2 ^ windowN from rfl, centerLoop_eq] at h
  rw [h, ite_eq_right (by omega), ite_eq_left (by omega), row_testBit windowN t (by omega) windowN]
  simp [center]

/-- The witness search: every period `P ≤ N/4` is broken within 32 steps after `N/2`. -/
def witnessCheck : Bool :=
  (List.range (windowN / 4)).all fun P => (List.range 32).any fun k =>
    centerBits.testBit (windowN / 2 + k) != centerBits.testBit (windowN / 2 + k + (P + 1))

theorem witnessCheck_true : witnessCheck = true := by decide +kernel

/-- **No small eventual period**: the center column has no eventual period `P ≤ N/4` whose
transient is at most `N/2`, for `N = windowN`. -/
theorem no_small_eventual_period (T P : Nat) (hP : 0 < P) (hPN : P ≤ windowN / 4)
    (hT : T ≤ windowN / 2) : ¬ ∀ t, T ≤ t → center (t + P) = center t := by
  intro h
  have hw := List.all_eq_true.1 witnessCheck_true (P - 1) (List.mem_range.2 (by omega))
  obtain ⟨k, hk, hne⟩ := List.any_eq_true.1 hw
  rw [List.mem_range] at hk
  rw [show P - 1 + 1 = P by omega] at hne
  have e := h (windowN / 2 + k) (by omega)
  rw [center_eq_bit _ (by simp [windowN] at hPN ⊢; omega),
    center_eq_bit _ (by simp [windowN]; omega)] at e
  simp [e] at hne

end Rule30Window
end Ruliology.CellularAutomata
