use cursive::theme::{BorderStyle, Palette};
use cursive::traits::With;
use cursive::views::{Dialog, EditView, LinearLayout, TextView};
use cursive::Cursive;

fn main() {
    let mut siv = cursive::default();

    // Start with a nicer theme than default
    siv.set_theme(cursive::theme::Theme {
        shadow: true,
        borders: BorderStyle::Simple,
        palette: Palette::default().with(|palette| {
            use cursive::theme::BaseColor::*;
            use cursive::theme::Color::TerminalDefault;
            use cursive::theme::PaletteColor::*;

            palette[Background] = TerminalDefault;
            palette[View] = TerminalDefault;
            palette[Primary] = White.dark();
            palette[TitlePrimary] = Blue.light();
            palette[Secondary] = Blue.light();
            palette[Highlight] = Blue.dark();
        }),
    });

    let layout = LinearLayout::vertical()
        .child(TextView::new("This is a dynamic theme example!"))
        .child(EditView::new().content("Woo! colors!"));

    siv.add_layer(
        Dialog::around(layout)
            .title("Theme example")
            .button("Change", |s| {
                // Change _something_ when the button is pressed.
                let mut theme = s.current_theme().clone();

                theme.shadow = !theme.shadow;
                theme.borders = match theme.borders {
                    BorderStyle::Simple => BorderStyle::Outset,
                    BorderStyle::Outset => BorderStyle::None,
                    BorderStyle::None => BorderStyle::Simple,
                };

                s.set_theme(theme);
            })
            .button("Quit", Cursive::quit),
    );

    siv.run();
}
