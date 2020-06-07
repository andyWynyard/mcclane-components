// import { Meta, Story, Preview } from '@storybook/addon-docs/blocks'
import React from 'react'
import { text, boolean, number } from '@storybook/addon-knobs'
import styled, { ThemeProvider } from 'styled-components'
import Typography from '../Typography'

// <Preview>
//   <Story name="Typography">
//     <Typography as={`h1`} color={`tomato`} bg={`green`}>
//       {text('Heading text', 'This is a heading')}
//     </Typography>
//   </Story>
// </Preview>

const theme = {
  colors: {
    primary: '#565656',
    secondary: '#f4f4f4',
  },
}

export default { title: 'Typography' }

export const typography = () => {
  return (
    <ThemeProvider theme={theme}>
      <Typography as={`h1`} color={theme.colors.secondary} bg={`green`} m={4}>
        {text('Heading text', 'This is a heading')}
      </Typography>
    </ThemeProvider>
  )
}
