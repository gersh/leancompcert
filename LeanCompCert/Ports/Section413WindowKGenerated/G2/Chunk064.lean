import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk064

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360857130840580614, 360857131053440872⟩, ⟨(-1818075425477992199), (-1818074501277628025)⟩, true⟩

def state01 : KState := ⟨⟨360877877864841053, 360877878078399463⟩, ⟨(-1950111126234702282), (-1950110197562661750)⟩, true⟩

def words00 : List Nat := [360573157579776743, 360573234330805109, 360573320071583314, 360573405785602340, 360573468013852233, 360573506315536042, 360573557059868455, 360573607788387563, 360573648718328699, 360573696172680752]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 6400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 6400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360558274367517963, 360558274581782360⟩, ⟨100635318168934937, 100636251369908045⟩, true⟩

def words01 : List Nat := [360573731311433759, 360573766439237480, 360573801025919166, 360573847740268932, 360573887968874335, 360573928184953614, 360573952226858438, 360573952452235191, 360573952452296332, 360573950010344651]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 6410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 6400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360859430866793588, 360859431081756972⟩, ⟨(-1834133823437294883), (-1834132885745352391)⟩, true⟩

def words02 : List Nat := [360573969237836880, 360573993029142673, 360574004595620972, 360574016158507378, 360574020588162670, 360574046681187011, 360574096832188898, 360574146967603336, 360574184909713625, 360574229264660821]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 6420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 6400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360914220931406872, 360914221147072236⟩, ⟨(-2187365122244635182), (-2187364180035537192)⟩, true⟩

def words03 : List Nat := [360574287304958583, 360574345327233188, 360574402212918080, 360574435387605203, 360574445161858963, 360574454933080320, 360574476334792891, 360574515574634378, 360574568324007140, 360574621057018590]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 6430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 6400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360821273366878764, 360821273583252814⟩, ⟨(-1590092321751283960), (-1590091374974735748)⟩, true⟩

def words04 : List Nat := [360574659252416290, 360574673775907931, 360574695226450327, 360574716670358280, 360574731724759552, 360574743890394150, 360574743890461632, 360574737230245132, 360574747788598338, 360574786003811684]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 6440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 6400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360646116795247776, 360646117012323358⟩, ⟨(-458264649510505295), (-458263698205484735)⟩, true⟩

def words05 : List Nat := [360574848072484335, 360574910121933934, 360574959385359881, 360575009740030135, 360575053736708008, 360575097719777746, 360575144320889882, 360575167376290662, 360575178359272929, 360575189338866388]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 6450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 6400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360767622493639342, 360767622711420921⟩, ⟨(-1244618330189876895), (-1244617374320609257)⟩, true⟩

def words06 : List Nat := [360575189338928181, 360575199471126829, 360575220805981650, 360575242134250406, 360575242875816557, 360575242875891290, 360575232211906796, 360575231990418904, 360575255265544494, 360575284993244348]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 6460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 6400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583377771307054, 360583377989801337⟩, ⟨(-50892421593040790), (-50891461109088324)⟩, true⟩

def words07 : List Nat := [360575302507484417, 360575320016320529, 360575361215810360, 360575417884380305, 360575455367173219, 360575492838402987, 360575513063190586, 360575523156947113, 360575524369173912, 360575525581051285]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 6470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 6400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360767729555359365, 360767729774560209⟩, ⟨(-1246230187779406178), (-1246229222713360136)⟩, true⟩

def words08 : List Nat := [360575550448862704, 360575576289649367, 360575590097844035, 360575603901788355, 360575611446666243, 360575635305613445, 360575665441001477, 360575695567115303, 360575706781768259, 360575736364806187]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 6480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 6400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨361093183309314434, 361093183529223630⟩, ⟨(-3360097101388180149), (-3360096131721399709)⟩, true⟩

def words09 : List Nat := [360575789511179650, 360575842641204418, 360575908212068439, 360575967690183404, 360576006831550652, 360576045960876075, 360576098915363907, 360576166121526289, 360576245662726846, 360576325179474146]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 6490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 6400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 6400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk064
