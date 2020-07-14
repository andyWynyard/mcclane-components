import { colors } from '../../defaultTheme'
import { StyledSystemProps } from '../GenericComponent'
import 'typeface-roboto'
import 'typeface-lato'

const fontFamilies: { heading: string; body: string } = {
  heading: 'Lato, serif',
  body: 'Roboto, sans-serif',
}

interface TypographyStyles {
  H1: StyledSystemProps
  H2: StyledSystemProps
  H3: StyledSystemProps
  H4: StyledSystemProps
  H5: StyledSystemProps
  LeadLarge: StyledSystemProps
  LeadSmall: StyledSystemProps
  Paragraph: StyledSystemProps
  ParagraphSmall: StyledSystemProps
  Link: StyledSystemProps
}

export const typographyStyles: TypographyStyles = {
  H1: {
    fontSize: [19, 20, 21, 22],
    fontWeight: 700,
    fontFamily: fontFamilies.heading,
    as: 'h1',
  },
  H2: {
    fontSize: [15, 16, 17, 18],
    fontWeight: 700,
    fontFamily: fontFamilies.heading,
    as: 'h2',
  },
  H3: {
    fontSize: [11, 12, 13, 14],
    fontWeight: 700,
    fontFamily: fontFamilies.heading,
    as: 'h3',
  },
  H4: {
    fontSize: [5, 7, 9, 10],
    fontWeight: 700,
    fontFamily: fontFamilies.heading,
    as: 'h4',
  },
  H5: {
    fontWeight: 700,
    fontSize: [3, 4, 6, 8],
    fontFamily: fontFamilies.heading,
    as: 'h5',
  },
  LeadSmall: {
    fontWeight: 500,
    fontSize: [5, 7, 9, 10],
    fontFamily: fontFamilies.heading,
    as: 'p',
  },
  LeadLarge: {
    fontWeight: 500,
    fontSize: [4, 5, 6, 8],
    fontFamily: fontFamilies.heading,
    as: 'p',
  },
  Paragraph: {
    fontSize: [1, 2, 2, 3],
    fontWeight: 300,
    fontFamily: fontFamilies.body,
    as: 'p',
  },
  ParagraphSmall: {
    fontSize: [0, 1, 1, 2],
    fontWeight: 300,
    fontFamily: fontFamilies.body,
    as: 'p',
  },
  Link: {
    fontWeight: 700,
    color: colors.primary,
    fontSize: [1, 2, 2, 3],
    fontFamily: fontFamilies.body,
  },
}
