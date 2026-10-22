import Foundation
import AppKit
import PDFKit

let path = CommandLine.arguments[1]
let out = CommandLine.arguments[2]
guard let doc = PDFDocument(url: URL(fileURLWithPath: path)) else {
    fatalError("Unreadable PDF")
}
let pages = (0..<doc.pageCount).map { doc.page(at: $0)! }
let text = pages.map { $0.string ?? "" }.joined(separator: "\n")
for needle in ["One closure application head per fragment", "Internal proof codes and budgets",
               "BudgetInternalization", "FiniteLiteralBank", "Comparison with Brown"] {
    guard text.contains(needle) else { fatalError("Missing section: \(needle)") }
}
let links = pages.flatMap { $0.annotations.compactMap { $0.url?.absoluteString } }
guard links.contains("https://doi.org/10.1145/2837614.2837623") else {
    fatalError("Missing original-paper link")
}
try text.write(toFile: out + "/pdf-text.txt", atomically: true, encoding: .utf8)
for index in Set([0, 7, 8, doc.pageCount - 3, doc.pageCount - 2, doc.pageCount - 1]).sorted() {
    let page = pages[index]
    let bounds = page.bounds(for: .mediaBox)
    let img = page.thumbnail(of: NSSize(width: bounds.width * 1.5, height: bounds.height * 1.5), for: .mediaBox)
    guard let data = img.tiffRepresentation, let bitmap = NSBitmapImageRep(data: data),
          let png = bitmap.representation(using: .png, properties: [:]) else {
        fatalError("Render failed")
    }
    try png.write(to: URL(fileURLWithPath: out + "/page-\(index + 1).png"))
}
print("PDF text, new sections, source link and page renders: PASS; pages=\(doc.pageCount)")
