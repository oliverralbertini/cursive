use crate::view::{View, ViewWrapper};

/// Applies a theme to the wrapped view.
pub struct ThemedView<T> {
    theme: crate::theme::Theme,
    view: T,
}

impl<T> ThemedView<T> {
    /// Wrap the given view with a theme.
    pub fn new(theme: crate::theme::Theme, view: T) -> Self {
        ThemedView { theme, view }
    }

    /// Retrieve the wrapped theme.
    pub fn get_theme(&self) -> &crate::theme::Theme {
        &self.theme
    }

    /// Sets a new theme for the wrapped view.
    pub fn set_theme(&mut self, theme: crate::theme::Theme) {
        self.theme = theme;
    }

    inner_getters!(self.view: T);
}

impl<T: View> ViewWrapper for ThemedView<T> {
    wrap_impl!(self.view: T);

    fn wrap_draw(&self, printer: &crate::Printer) {
        printer.theme(&self.theme).with_style(
            crate::theme::ColorStyle::primary(),
            |printer| {
                self.view.draw(printer);
            },
        );
    }
}

crate::recipe!(with theme, |config, context| {
    let theme = context.resolve(config)?;
    Ok(move |view| ThemedView::new(theme, view))
});
