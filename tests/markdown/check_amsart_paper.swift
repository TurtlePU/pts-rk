import Foundation
import PDFKit

let doc = PDFDocument(url: URL(fileURLWithPath: CommandLine.arguments[1]))!
let page = doc.page(at: 0)!
func selection(_ text: String) -> PDFSelection {
    doc.findString(text, withOptions: []).first!
}
let date = selection("October 16, 2026")
let classification = selection("2020 Mathematics Subject Classification")
assert(date.pages.first === page && classification.pages.first === page)
assert(date.bounds(for: page).minY > classification.bounds(for: page).minY)
assert(date.bounds(for: page).maxY < page.bounds(for: .mediaBox).height / 3)
assert(page.string!.contains("Date: October 16, 2026."))
print("AMS first-page date/classification footnote order: PASS")
