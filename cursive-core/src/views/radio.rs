use crate::builder::{Config, Context, Error, FromConfig};
use crate::{
    direction::Direction,
    event::{Event, EventResult, Key, MouseButton, MouseEvent},
    theme::ColorStyle,
    view::{CannotFocus, View},
    Cursive, Printer, Vec2, With,
};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

type Callback<T> = dyn Fn(&mut Cursive, &T);

struct SharedState<T> {
    selection: usize,
    values: Vec<Rc<T>>,

    on_change: Option<Rc<Callback<T>>>,
}

impl<T> SharedState<T> {
    pub fn selection(&self) -> Rc<T> {
        Rc::clone(&self.values[self.selection])
    }
}

/// Group to coordinate multiple radio buttons.
///
/// A `RadioGroup` is used to create and manage [`RadioButton`]s.
///
/// A `RadioGroup` can be cloned; it will keep pointing to the same group.
pub struct RadioGroup<T> {
    // Given to every child button
    state: Rc<RefCell<SharedState<T>>>,
}

impl<T> Clone for RadioGroup<T> {
    fn clone(&self) -> Self {
        Self {
            state: Rc::clone(&self.state),
        }
    }
}

impl<T: 'static> Default for RadioGroup<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: 'static> RadioGroup<T> {
    /// Creates an empty group for radio buttons.
    pub fn new() -> Self {
        RadioGroup {
            state: Rc::new(RefCell::new(SharedState {
                selection: 0,
                values: Vec::new(),
                on_change: None,
            })),
        }
    }

    /// Adds a new button to the group.
    ///
    /// The button will display `label` next to it, and will embed `value`.
    pub fn button<S: Into<String>>(
        &mut self,
        value: T,
        label: S,
    ) -> RadioButton<T> {
        let count = self.state.borrow().values.len();
        self.state.borrow_mut().values.push(Rc::new(value));
        RadioButton::new(Rc::clone(&self.state), count, label.into())
    }

    /// Returns the id of the selected button.
    ///
    /// Buttons are indexed in the order they are created, starting from 0.
    pub fn selected_id(&self) -> usize {
        self.state.borrow().selection
    }

    /// Returns the value associated with the selected button.
    pub fn selection(&self) -> Rc<T> {
        self.state.borrow().selection()
    }

    /// Sets a callback to be used when the selection changes.
    pub fn set_on_change<F: 'static + Fn(&mut Cursive, &T)>(
        &mut self,
        on_change: F,
    ) {
        self.state.borrow_mut().on_change = Some(Rc::new(on_change));
    }

    /// Sets a callback to be used when the selection changes.
    ///
    /// Chainable variant.
    #[must_use]
    pub fn on_change<F: 'static + Fn(&mut Cursive, &T)>(
        self,
        on_change: F,
    ) -> Self {
        self.with(|s| s.set_on_change(on_change))
    }
}

impl RadioGroup<String> {
    /// Adds a button, using the label itself as value.
    pub fn button_str<S: Into<String>>(
        &mut self,
        text: S,
    ) -> RadioButton<String> {
        let text = text.into();
        self.button(text.clone(), text)
    }
}

/// Variant of `Checkbox` arranged in group.
///
/// `RadioButton`s are managed by a [`RadioGroup`]. A single group can contain
/// several radio buttons, but only one button per group can be active at a
/// time.
///
/// `RadioButton`s are not created directly, but through
/// [`RadioGroup::button`].
pub struct RadioButton<T> {
    state: Rc<RefCell<SharedState<T>>>,
    id: usize,
    enabled: bool,
    label: String,
}

impl<T: 'static> RadioButton<T> {
    impl_enabled!(self.enabled);

    fn new(
        state: Rc<RefCell<SharedState<T>>>,
        id: usize,
        label: String,
    ) -> Self {
        RadioButton {
            state,
            id,
            enabled: true,
            label,
        }
    }

    /// Returns `true` if this button is selected.
    pub fn is_selected(&self) -> bool {
        self.state.borrow().selection == self.id
    }

    /// Selects this button, un-selecting any other in the same group.
    pub fn select(&mut self) -> EventResult {
        let mut state = self.state.borrow_mut();
        state.selection = self.id;
        if let Some(ref on_change) = state.on_change {
            let on_change = Rc::clone(on_change);
            let value = state.selection();
            EventResult::with_cb(move |s| on_change(s, &value))
        } else {
            EventResult::Consumed(None)
        }
    }

    /// Selects this button, un-selecting any other in the same group.
    ///
    /// Chainable variant.
    #[must_use]
    pub fn selected(self) -> Self {
        self.with(|s| {
            // Ignore the potential callback here
            s.select();
        })
    }

    fn draw_internal(&self, printer: &Printer) {
        printer.print((0, 0), "( )");
        if self.is_selected() {
            printer.print((1, 0), "X");
        }

        if !self.label.is_empty() {
            // We want the space to be highlighted if focused
            printer.print((3, 0), " ");
            printer.print((4, 0), &self.label);
        }
    }

    fn req_size(&self) -> Vec2 {
        if self.label.is_empty() {
            Vec2::new(3, 1)
        } else {
            Vec2::new(3 + 1 + self.label.len(), 1)
        }
    }

    /// Build a button from a radio group.
    ///
    /// Equivalent to `group.button(value, label)`
    pub fn from_group<S: Into<String>>(
        group: &mut RadioGroup<T>,
        value: T,
        label: S,
    ) -> Self {
        group.button(value, label)
    }
}

impl RadioButton<String> {
    /// Build a button from a radio group.
    ///
    /// Equivalent to `group.button_str(label)`
    pub fn from_group_str<S: Into<String>>(
        group: &mut RadioGroup<String>,
        label: S,
    ) -> Self {
        group.button_str(label)
    }
}

impl<T: 'static> View for RadioButton<T> {
    fn required_size(&mut self, _: Vec2) -> Vec2 {
        self.req_size()
    }

    fn take_focus(
        &mut self,
        _: Direction,
    ) -> Result<EventResult, CannotFocus> {
        self.enabled.then(EventResult::consumed).ok_or(CannotFocus)
    }

    fn draw(&self, printer: &Printer) {
        if self.enabled && printer.enabled {
            printer.with_selection(printer.focused, |printer| {
                self.draw_internal(printer)
            });
        } else {
            printer.with_color(ColorStyle::secondary(), |printer| {
                self.draw_internal(printer)
            });
        }
    }

    fn on_event(&mut self, event: Event) -> EventResult {
        if !self.enabled {
            return EventResult::Ignored;
        }

        match event {
            Event::Key(Key::Enter) | Event::Char(' ') => self.select(),
            Event::Mouse {
                event: MouseEvent::Release(MouseButton::Left),
                position,
                offset,
            } if position.fits_in_rect(offset, self.req_size()) => {
                self.select()
            }
            _ => EventResult::Ignored,
        }
    }
}

thread_local! {
    pub static GLOBAL_GROUPS: RefCell<HashMap<String, RadioGroup<String>>> = RefCell::new(HashMap::new());
}

impl FromConfig for RadioGroup<String> {
    fn from_config(config: &Config, context: &Context) -> Result<Self, Error> {
        let name: String = context.resolve(config)?;

        let group = std::thread::LocalKey::with(&GLOBAL_GROUPS, |groups| {
            groups
                .borrow_mut()
                .entry(name)
                .or_insert_with(RadioGroup::new)
                .clone()
        });

        Ok(group)
    }
}

#[cursive_macros::recipe(RadioButton::from_group_str(&mut group, label))]
struct Recipe {
    group: RadioGroup<String>,
    label: String,
}
