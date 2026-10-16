import Foundation
import AppKit
import PDFKit

let doc = PDFDocument(url: URL(fileURLWithPath: CommandLine.arguments[1]))!
let page = doc.page(at: 0)!
let first = doc.findString("We present", withOptions: []).first!
// Use actual rendered line starts: font-size changes can move hyphenation.
let lines = page.string!.components(separatedBy: "\n")
let index = lines.firstIndex(where: { $0.hasPrefix("We present") })!
let prefix = String(lines[index + 1].prefix(12))
let next = doc.findString(prefix, withOptions: []).first!
print("Abstract first/continuation x:", first.bounds(for: page).minX, next.bounds(for: page).minX)
assert(abs(first.bounds(for: page).minX - next.bounds(for: page).minX) < 1)
let body = doc.findString("Pure type systems", withOptions: []).first!
let fontSize: (PDFSelection) -> CGFloat = {
    ($0.attributedString!.attribute(.font, at: 0, effectiveRange: nil) as! NSFont).pointSize
}
print("Abstract/body font size:", fontSize(first), fontSize(body))
assert(abs(fontSize(first) / fontSize(body) - 0.9) < 0.001)
let date = doc.findString("October 16, 2026", withOptions: []).first!
print("Date/body font size:", fontSize(date), fontSize(body))
assert(abs(fontSize(date) - fontSize(body)) < 0.01)
if CommandLine.arguments.count > 2 {
    let baseline = PDFDocument(url: URL(fileURLWithPath: CommandLine.arguments[2]))!
    let title = "A sound pure type system with ranks as sorts"
    let now = doc.findString(title, withOptions: []).first!.bounds(for: page).minY
    let before = baseline.findString(title, withOptions: []).first!
        .bounds(for: baseline.page(at: 0)!).minY
    print("Title raised by:", now - before, "PDF pt")
    assert(abs((now - before) - fontSize(body)) < 0.05)
}
// Prose following the list-local display must not be typeset as mathematics.
let proofProse = doc.findString("This is true by structural induction", withOptions: []).first!
assert(abs(fontSize(proofProse) - fontSize(body)) < 0.01)
let text = (0..<doc.pageCount).map { doc.page(at: $0)!.string ?? "" }.joined(separator: "\n")
assert(text.components(separatedBy: "formerly Coq").count == 2)
print("PDF abstract layout, proof prose and unique Rocq alias: PASS")
